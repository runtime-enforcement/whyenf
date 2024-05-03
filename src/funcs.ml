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
    arg_tts: (string * Dom.tt) list;
    ret_tt: Dom.tt;
    kind: kind;
  }

let to_string name func =
  let f acc (var, tt) = acc ^ "," ^ var ^ ":" ^ (Dom.tt_to_string tt) in
  Printf.sprintf "%s(%s) : %s" name
    (String.drop_prefix (List.fold func.arg_tts ~init:"" ~f) 1)
    (Dom.tt_to_string func.ret_tt)

let builtins =
  [
    ("eq",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (if i == j then 1 else 0))
    });
    ("neq",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (if i != j then 1 else 0))
    });
    ("add",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i+j))
    });
    ("sub",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i-j))
    });
    ("mul",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i*j))
    });
    ("div",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i/j))
    });
    ("pow",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (Int.pow i j))
    });
    ("feq",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Int (if i == j then 1 else 0))
    });
    ("fneq",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Int (if i != j then 1 else 0))
    });
    ("fadd",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i+.j))
    });
    ("fsub",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i-.j))
    });
    ("fmul",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i*.j))
    });
    ("fdiv",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i/.j))
    });
    ("fpow",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TFloat); ("y", Dom.TFloat)];
       ret_tt  = Dom.TFloat;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Float i, Dom.Float j -> Float (i ** j))
    });
    ("seq",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TStr); ("y", Dom.TStr)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Str i, Dom.Str j -> Int (if i == j then 1 else 0))
    });
    ("sneq",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TStr); ("y", Dom.TStr)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Str i, Dom.Str j -> Int (if i != j then 1 else 0))
    });
    ("conc",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TStr); ("y", Dom.TStr)];
       ret_tt  = Dom.TStr;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Str i, Dom.Str j -> Str (i ^ j))
    });
    ("substr",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TStr); ("start", Dom.TInt); ("end", Dom.TInt)];
       ret_tt  = Dom.TStr;
       kind    = Builtin (fun [x;start;end_] ->
                     match x, start, end_ with
                       Dom.Str i, Dom.Int j, Dom.Int k -> Str (String.slice i j k))});
  ]
