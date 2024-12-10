open Core

open MFOTL_lib

module Ctxt = Ctxt.Make(Dom)

module Python = struct

  let m = ref None
  
  let load f =
    Py.initialize ~version:3 ();
    m := Some (Py.Import.exec_code_module_from_string ~name:"funcs" (In_channel.read_all f))

  let string_of_dom = function
    | Dom.Int i -> string_of_int i
    | Dom.Float f -> string_of_float f
    | Dom.Str s -> "\"" ^ String.escaped s ^ "\""

  let dom_of_object tt o = match tt with
    | Dom.TInt -> Dom.Int (Py.Int.to_int o)
    | Dom.TFloat -> Dom.Float (Py.Float.to_float o)
    | Dom.TStr -> Dom.Str (Py.String.to_string o)

  let dom_list_list_of_object tts o =
    List.map ~f:(fun o -> List.map2_exn ~f:dom_of_object tts (Py.List.to_list o)) (Py.List.to_list o)

  let create_python_call_string f ds =
    Printf.sprintf "%s(%s)" f (String.concat ~sep:", " (List.map ds ~f:string_of_dom))

  let create_python_call_list_string f dss =
    Printf.sprintf "%s([%s])" f
      (String.concat ~sep:", "
         (List.map dss
            ~f:(fun ds -> "[" ^ String.concat ~sep:", " (List.map ds ~f:string_of_dom) ^ "]")))

  let eval string =
    match !m with
    | Some m -> Py.Run.eval ~globals:(Py.Module.get_dict m) string
    | None -> raise (Invalid_argument "Python module must be loaded to call externally defined functions. Pass filename of Python module through -func option.")
      
  let call f ds tt = dom_of_object tt (eval (create_python_call_string f ds))
  let tcall f dss tts =
    let dss = dom_list_list_of_object tts (eval (create_python_call_list_string f dss)) in
    (*print_endline (Etc.string_list_to_string (List.map ~f:(fun x -> "[" ^ Etc.string_list_to_string (List.map ~f:Dom.to_string x) ^ "]") dss));*)
    dss
  
  let retrieve_db f tts =
    let const_list_list = eval (create_python_call_string f []) in
    Py.List.to_list_map (fun const_list -> List.map2_exn tts (Py.List.to_list const_list) ~f:dom_of_object) const_list_list
    
end

type kind =
  | Builtin of (Dom.t list -> Dom.t)
  | Table
  | External

type t =
  { arity: int;
    arg_ttts: (string * Ctxt.ttt) list;
    ret_ttts: Ctxt.ttt list;
    kind: kind;
    strict: bool
  }

let to_string name func =
  let f acc (var, tt) = acc ^ "," ^ var ^ ":" ^ (Ctxt.ttt_to_string tt) in
  Printf.sprintf "%s(%s) : %s" name
    (String.drop_prefix (List.fold func.arg_ttts ~init:"" ~f) 1)
    (Etc.list_to_string "" (fun _ -> Ctxt.ttt_to_string) func.ret_ttts)

let is_eq = function
  | "eq" | "feq" | "seq" -> true
  | _ -> false

let poly_fun2 f f_name = function
  | [x; y] -> f x y
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s called with %d arguments, expected 2"
                     f_name (List.length l)))

let tt_string l =
  if List.length l = 1 then
    Printf.sprintf "type %s" (Dom.tt_to_string (Dom.tt_of_domain (List.hd_exn l)))
  else
    Printf.sprintf "types (%s)"
      (String.concat ~sep:", " (List.map l ~f:(fun d -> Dom.tt_to_string (Dom.tt_of_domain d))))

let int_fun1 f f_name = function
  | [Dom.Int x] -> f x
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s takes an argument of type int, but it is called with arguments of %s"
                     f_name (tt_string l)))

let int_fun2 f f_name = function
  | [Dom.Int x; Int y] -> f x y
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s takes arguments of types (int, int), but it is called with arguments of %s"
                     f_name (tt_string l)))

let float_fun1 f f_name = function
  | [Dom.Float x] -> f x
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s takes an argument of type float, but it is called with arguments of %s"
                     f_name (tt_string l)))

let float_fun2 f f_name = function
  | [Dom.Float x; Float y] -> f x y
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s takes arguments of types (float, float), but it is called with arguments of %s"
                     f_name (tt_string l)))

let string_fun2 f f_name = function
  | [Dom.Str x; Str y] -> f x y
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s takes arguments of types (str, str), but it is called with arguments of %s"
                     f_name (tt_string l)))

let string_int_int_fun f f_name = function
  | [Dom.Str i; Int j; Int k] -> f i j k
  | l -> raise (Errors.FunctionError 
                  (Printf.sprintf "Function %s takes arguments of types (str, int, int), but it is called with arguments of %s"
                     f_name (tt_string l)))
  
let builtins =
  [
    ("eq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttts = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (poly_fun2 (fun x y -> Dom.Int (if Dom.equal x y then 1 else 0)) "eq");
       strict  = true;
    });
    ("neq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttts = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (poly_fun2 (fun x y -> Dom.Int (if Dom.equal x y then 0 else 1)) "neq");
       strict  = true;
    });
    ("lt",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (poly_fun2 (fun x y -> Dom.Int (if Dom.lt x y then 1 else 0)) "lt");
       strict  = true;
    });
    ("leq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (poly_fun2 (fun x y -> Dom.Int (if Dom.leq x y then 1 else 0)) "leq");
       strict  = true;
    });
    ("gt",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (poly_fun2 (fun x y -> Dom.Int (if Dom.gt x y then 1 else 0)) "gt");
       strict  = true;
    });
    ("geq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (poly_fun2 (fun x y -> Dom.Int (if Dom.geq x y then 1 else 0)) "geq");
       strict  = true;
    });
    ("add",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun2 (fun i j -> Dom.Int (i+j)) "add");
       strict  = false;
    });
    ("sub",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun2 (fun i j -> Dom.Int (i-j)) "sub");
       strict  = false;
    });
    ("usub",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun1 (fun i -> Dom.Int i) "usub");
       strict  = true;
    });
    ("not",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun1 (fun i -> Dom.Int Int.(if i = 0 then 1 else 0)) "not");
       strict  = true;
    });
    ("mul",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun2 (fun i j -> Dom.Int (i*j)) "mul");
       strict  = false;
    });
    ("div",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun2 (fun i j -> Dom.Int (i/j)) "div");
       strict  = false;
    });
    ("pow",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (int_fun2 (fun i j -> Dom.Int (Int.pow i j)) "pow");
       strict  = false;
    });
    ("fadd",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttts  = [Ctxt.TConst Dom.TFloat];
       kind    = Builtin (float_fun2 (fun i j -> Dom.Float (i+.j)) "fadd");
       strict  = false;
    });
    ("fsub",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttts  = [Ctxt.TConst Dom.TFloat];
       kind    = Builtin (float_fun2 (fun i j -> Dom.Float (i-.j)) "fsub");
       strict  = false;
    });
    ("ufsub",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat)];
       ret_ttts  = [Ctxt.TConst Dom.TFloat];
       kind    = Builtin (float_fun1 (fun i -> Dom.Float (-.i)) "ufsub");
       strict  = true;
    });
    ("fmul",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttts  = [Ctxt.TConst Dom.TFloat];
       kind    = Builtin (float_fun2 (fun i j -> Dom.Float (i*.j)) "fmul");
       strict  = false;
    });
    ("fdiv",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttts  = [Ctxt.TConst Dom.TFloat];
       kind    = Builtin (float_fun2 (fun i j -> Dom.Float (i/.j)) "fdiv");
       strict  = false;
    });
    ("fpow",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttts  = [Ctxt.TConst Dom.TFloat];
       kind    = Builtin (float_fun2 (fun i j -> Dom.Float (i ** j)) "fpow");
       strict  = false;
    });
    ("conc",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TStr); ("y", Ctxt.TConst Dom.TStr)];
       ret_ttts  = [Ctxt.TConst Dom.TStr];
       kind    = Builtin (string_fun2 (fun i j -> Dom.Str (i ^ j)) "conc");
       strict  = false;
    });
    ("substr",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TStr); ("start", Ctxt.TConst Dom.TInt); ("end", Ctxt.TConst Dom.TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TStr];
       kind    = Builtin (string_int_int_fun (fun i j k -> Dom.Str (String.slice i j k)) "substr");
       strict  = false;
    });
    ("match",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TStr); ("r", Ctxt.TConst Dom.TStr)];
       ret_ttts  = [Ctxt.TConst Dom.TInt];
       kind    = Builtin (string_fun2 (fun i j -> 
                     if Str.string_match (Str.regexp j) i 0 then Dom.Int 1 else Dom.Int 0) "match");
       strict  = false;
    });
    ("string_of_int",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TInt)];
       ret_ttts  = [Ctxt.TConst Dom.TStr];
       kind    = Builtin (int_fun1 (fun i -> Dom.Str (string_of_int i)) "string_of_int");
       strict  = false;
    });
    ("string_of_float",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TFloat)];
       ret_ttts  = [Ctxt.TConst TStr];
       kind    = Builtin (float_fun1 (fun i -> Dom.Str (string_of_float i)) "string_of_float");
       strict  = false;
    });
    ("int_of_float",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TFloat)];
       ret_ttts  = [Ctxt.TConst TInt];
       kind    = Builtin (float_fun1 (fun i -> Dom.Int (int_of_float i)) "int_of_float");
       strict  = false;
    });
    ("float_of_int",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TInt)];
       ret_ttts = [Ctxt.TConst TFloat];
       kind    = Builtin (int_fun1 (fun i -> Dom.Float (float_of_int i)) "float_of_int");
       strict  = false;
    });
  ]

