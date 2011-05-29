(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/spec.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** Data structures used to represent specifications.
  Also, their pretty-printing. *)
  
module ExceptionMap = Map.Make (struct type t = string let compare = compare end)

type catch_labels =
  {
    from_label: string;
    to_label: string;
    with_label: string; 
  }

type excep_post = Psyntax.pform ExceptionMap.t 

type spec = 
    { pre : Psyntax.pform;
      post : Psyntax.pform;
      excep : excep_post }


let mk_spec pre post excep = 
    { pre = pre;
      post = post;
      excep = excep }

let spec2str ppf (spec: spec)  = 
  let po s = Format.fprintf ppf "@\n@[<4>{%a}@]" Psyntax.string_form s in
  let po_excep t s = Format.fprintf ppf "@\n@[<4>{%s:%a}@]" t Psyntax.string_form s in
  po spec.pre; po spec.post;
  ExceptionMap.iter (fun t s -> po_excep t s) spec.excep

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  
let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1

let parameter n = "@parameter"^(string_of_int n)^":"
let parameter_var n = (Vars.concretep_str (parameter n))
