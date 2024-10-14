open Core

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

  let create_python_call_string f ds =
    Printf.sprintf "%s(%s)" f (String.concat ~sep:", " (List.map ds ~f:string_of_dom))

  let eval string =
    match !m with
    | Some m -> Py.Run.eval ~globals:(Py.Module.get_dict m) string
    | None -> raise (Invalid_argument "Python module must be loaded to call externally defined functions. Pass filename of Python module through -func option.")
      
  let call f ds tt = dom_of_object tt (eval (create_python_call_string f ds))

  let retrieve_db f tts =
    let const_list_list = eval (create_python_call_string f []) in
    Py.List.to_list_map (fun const_list -> List.map2_exn tts (Py.List.to_list const_list) ~f:dom_of_object) const_list_list
    
end

type kind =
  | Builtin of (Dom.t list -> Dom.t)
  | External

type t =
  { arity: int;
    arg_ttts: (string * Ctxt.ttt) list;
    ret_ttt: Ctxt.ttt;
    kind: kind;
    strict: bool
  }

let to_string name func =
  let f acc (var, tt) = acc ^ "," ^ var ^ ":" ^ (Ctxt.ttt_to_string tt) in
  Printf.sprintf "%s(%s) : %s" name
    (String.drop_prefix (List.fold func.arg_ttts ~init:"" ~f) 1)
    (Ctxt.ttt_to_string func.ret_ttt)

let eq [x;y]  = Dom.Int (if Dom.equal x y then 1 else 0)
let neq [x;y] = Dom.Int (if Dom.equal x y then 0 else 1)
let lt [x;y] = Dom.Int (if x < y then 1 else 0)
let leq [x;y] = Dom.Int (if x <= y then 1 else 0)
let gt [x;y] = Dom.Int (if x > y then 1 else 0)
let geq [x;y] = Dom.Int (if x >= y then 1 else 0)

let is_eq = function
  | "eq" | "feq" | "seq" -> true
  | _ -> false
  
let builtins =
  [
    ("eq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin eq;
       strict  = true;
    });
    ("neq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin neq;
       strict  = true;
    });
    ("lt",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j ->
                                         Int (if i < j then 1 else 0));
       strict  = true;
    });
    ("leq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j ->
                                         Int (if i <= j then 1 else 0));
       strict  = true;
    });
    ("gt",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j ->
                                         Int (if i > j then 1 else 0));
       strict  = true;
    });
    ("geq",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TVar "a"); ("y", Ctxt.TVar "a")];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j ->
                                         Int (if i >= j then 1 else 0));
       strict  = true;
    });
    ("add",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i+j));
       strict  = false;
    });
    ("sub",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i-j));
       strict  = false;
    });
    ("usub",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x] -> match x with Dom.Int i -> Int (-i));
       strict  = true;
    });
    ("mul",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i*j));
       strict  = false;
    });
    ("div",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i/j));
       strict  = false;
    });
    ("pow",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TInt); ("y", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (Int.pow i j));
       strict  = false;
    });
    ("fadd",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttt  = Ctxt.TConst Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i+.j));
       strict  = false;
    });
    ("fsub",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttt  = Ctxt.TConst Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i-.j));
       strict  = false;
    });
    ("ufsub",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat)];
       ret_ttt  = Ctxt.TConst Dom.TFloat;
       kind    = Builtin (fun [x] -> match x with Dom.Float i -> Float (-.i));
       strict  = true;
    });
    ("fmul",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttt  = Ctxt.TConst Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i*.j));
       strict  = false;
    });
    ("fdiv",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttt  = Ctxt.TConst Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i/.j));
       strict  = false;
    });
    ("fpow",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TFloat); ("y", Ctxt.TConst Dom.TFloat)];
       ret_ttt  = Ctxt.TConst Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i ** j));
       strict  = false;
    });
    ("conc",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TStr); ("y", Ctxt.TConst Dom.TStr)];
       ret_ttt  = Ctxt.TConst Dom.TStr;
       kind    = Builtin (fun [Str i; Str j] -> Str (i ^ j));
       strict  = false;
    });
    ("substr",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TStr); ("start", Ctxt.TConst Dom.TInt); ("end", Ctxt.TConst Dom.TInt)];
       ret_ttt  = Ctxt.TConst Dom.TStr;
       kind    = Builtin (fun [Str i; Int j; Int k] -> Str (String.slice i j k));
       strict  = false;
    });
    ("match",
     {
       arity   = 2;
       arg_ttts = [("x", Ctxt.TConst Dom.TStr); ("r", Ctxt.TConst Dom.TStr)];
       ret_ttt  = Ctxt.TConst Dom.TInt;
       kind    = Builtin (fun [Str i; Str j] ->
                     if Str.string_match (Str.regexp j) i 0 then Dom.Int 1 else Dom.Int 0);
       strict  = false;
    });
    ("string_of_int",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TInt)];
       ret_ttt  = Ctxt.TConst Dom.TStr;
       kind    = Builtin (fun [Int i] -> Str (string_of_int i));
       strict  = false;
    });
    ("string_of_float",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TFloat)];
       ret_ttt  = Ctxt.TConst TStr;
       kind    = Builtin (fun [Float i] -> Str (string_of_float i));
       strict  = false;
    });
    ("int_of_float",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TFloat)];
       ret_ttt  = Ctxt.TConst TInt;
       kind    = Builtin (fun [Float i] -> Int (int_of_float i));
       strict  = false;
    });
    ("float_of_int",
     {
       arity   = 1;
       arg_ttts = [("x", Ctxt.TConst TInt)];
       ret_ttt = Ctxt.TConst TFloat;
       kind    = Builtin (fun [Int i] -> Float (float_of_int i));
       strict  = false;
    });
  ]

