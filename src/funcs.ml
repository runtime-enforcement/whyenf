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

  let create_python_string f ds =
    Printf.sprintf "%s(%s)" f (String.concat ~sep:", " (List.map ds ~f:string_of_dom))
      
  let call f ds tt =
    match !m with
    | Some m -> print_endline (create_python_string f ds);
                dom_of_object tt (Py.Run.eval ~globals:(Py.Module.get_dict m) (create_python_string f ds))
    | None -> raise (Invalid_argument "Python module must be loaded to call externally defined functions. Pass filename of Python module through -func option.")
    
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
    ("add",
     {
       arity   = 2;
       arg_tts = [("x", Dom.TInt); ("y", Dom.TInt)];
       ret_tt  = Dom.TInt;
       kind    = Builtin (fun [x;y] -> match x, y with Dom.Int i, Dom.Int j -> Int (i+j))
    })
  ]
