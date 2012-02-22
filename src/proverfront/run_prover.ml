(********************************************************
   This file is part of coreStar
        src/proverfront/run.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Congruence
open Debug
open Format
open Load_logic
open Psyntax

let program_file_name = ref "";;
let logic_file_name = ref "";;
let abstraction_logic_file_name = ref "";;

let arg_list = Config.args_default @ 
  [ ("-l", Arg.Set_string(logic_file_name), "logic file name");
    ("-a", Arg.Set_string(abstraction_logic_file_name), "abstraction logic file name");]


let main () =
  let usage_msg="Usage: -l <logic_file_name> -a <abstraction_logic_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else 
    if !Config.smt_run then Smt.smt_init(); 
    (* Load abstract interpretation plugins *)
    List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;

    let l1,l2,cn = load_logic !logic_file_name in 
    let logic = {empty_logic with seq_rules = l1; rw_rules=l2; consdecl = cn} in
    let l1,l2,cn = load_logic !abstraction_logic_file_name in 
    let abs_logic = {empty_logic with seq_rules = l1; rw_rules=l2; consdecl = cn} in
    let lexbuf = Lexing.from_channel stdin in
    let is_parsing = ref true in
    try
        while !is_parsing do
            let question = System.parse_chan Parser.single_question Lexer.token
                   !program_file_name lexbuf in
            match question with
            | None -> is_parsing := false
            | Some(question) ->
                    match question with 
                    | Psyntax.Implication (heap1,heap2) ->
                        if (Sepprover.implies_opt logic (Sepprover.convert heap1) heap2)
                        then Printf.printf("1\n") else Printf.printf("0\n");
                        flush stdout;
                        if log log_prove then (
                          fprintf logf "@[";
                          Prover.pprint_proof logf;
                          fprintf logf "@.")
                    | Psyntax.Frame (heap1, heap2)  -> 
                        let x = Sepprover.frame_opt logic 
                            (Sepprover.convert_wo_eqs heap1) heap2 in 
                        (match x with None -> Printf.fprintf stderr "Can't find frame!" | Some
                        x -> List.iter (fun form -> printf "%a@.ENTER@."
                        Sepprover.string_inner_form  form) x;
                        );
                        printf "END@.ENTER@.";
                        flush stdout;
                        if log log_prove then (
                          fprintf logf "@[";
                          Prover.pprint_proof logf;
                          fprintf logf "@.")
                    | Psyntax.SpecAss (vl, precond, postcond, preheap, il) ->
                        let spec = Spec.mk_spec precond postcond Spec.ClassMap.empty in
                        let sub' = Symexec.param_sub il in
                        let spec' = Specification.sub_spec sub' spec in
                        let heap = (Sepprover.lift_inner_form (match Sepprover.convert preheap with Some x -> x)) in
                        let hs = Specification.jsr logic heap spec' false in
                        let hs = match hs with | None -> [] | Some hs -> hs in
                        let hs =
                            match vl with 
                            | [] -> hs
                            | vs -> List.map (Symexec.eliminate_ret_vs "$ret_" vs) hs
                        in
                        List.iter (fun form -> printf "%a@.ENTER@."
                        Sepprover.string_inner_form_af form) hs;
                        printf "END@.ENTER@.";
                        flush stdout;
                    | Psyntax.Abs (heap1)  ->
                        let x = Sepprover.abs_opt abs_logic (Sepprover.convert_wo_eqs heap1) in 
                        List.iter (fun form -> printf "%a@.ENTER@." Sepprover.string_inner_form form) x;
                        printf "END@.ENTER@.";
                        flush stdout;
                        if log log_prove then (
                          fprintf logf "@[";
                          Prover.pprint_proof logf;
                          fprintf logf "@.")
                    | Psyntax.Inconsistency (heap1) ->
                        if Sepprover.inconsistent_opt logic (Sepprover.convert heap1) 
                        then printf("Inconsistent!\n\n") else printf("Consistent!\n\n");
                        if log log_prove then (
                          fprintf logf "@[";
                          Prover.pprint_proof logf;
                          fprintf logf "@.")
                    | Psyntax.Equal (heap,arg1,arg2) -> ()
                    
                    | Psyntax.Abduction (heap1, heap2)  -> 
                      let x = (Sepprover.abduction_opt logic (Sepprover.convert heap1) heap2) in 
                      (match x with 
                        | None -> Printf.fprintf stderr "Can't find antiframe!\n"; flush stderr
                        | Some ls -> 
                          List.iter (fun inner_form_antiform -> 
                                  Printf.printf "%s" ""; Format.printf "%a@.ENTER@." Sepprover.string_inner_form_af inner_form_antiform) ls;
                      );
                      printf "END@.ENTER@.";
                      flush stdout;
        done
    with End_of_file -> ()

let _ = main ()
