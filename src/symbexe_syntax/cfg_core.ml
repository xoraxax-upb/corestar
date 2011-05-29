(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/cfg_core.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** Data structures for representing flowgraphs of the core languages.
  Also, utilities to build such flowgraphs and to pretty-print them. *)

open Core
open Pprinter_core
open Spec

let cfg_debug () = false

(* {{{ data structure to represent (core) flowgraphs *)

(* A node in the flowgraph. The fields [succs] and [preds] are filled 
  by [Cfg_core.stmts_to_cfg]. *)
type cfg_node = { 
  skind: core_statement;
  sid: int;  
  mutable succs: cfg_node list; 
  mutable preds: cfg_node list;
  mutable esuccs: (cfg_node list) ExceptionMap.t;
  mutable epreds: (cfg_node list) ExceptionMap.t
}

(* data structure to represent (core) flowgraphs }}} *)
(* {{{ utils for building flowgraphs *)
let mk_node : core_statement -> cfg_node =
  let x = ref 0 in
  fun stmt ->
    incr x;
    { skind = stmt; sid = !x; succs = []; preds = []; esuccs = ExceptionMap.empty; epreds = ExceptionMap.empty }
    
let exception_cfg (stmts : cfg_node list) (emap : (catch_labels list) ExceptionMap.t) : unit =
  let l2s = Hashtbl.create 11 in (* maps labels to statements *)
  let al = function
    | {skind = Label_stmt_core l} as s -> Hashtbl.add l2s l s
    | _ -> () in
  let connect fid m n = (* adds an edge from [m] to [n] *)
    let old_value = try ExceptionMap.find fid m.esuccs with Not_found -> [] in
    let new_value = n :: old_value in
    m.esuccs <- ExceptionMap.add fid new_value m.esuccs; 
    let old_value = try ExceptionMap.find fid n.epreds with Not_found -> [] in
    let new_value = m :: old_value in
    n.epreds <- ExceptionMap.add fid new_value n.epreds 
  in
  let rec process stmts end_l catch_cfg_node fid =
    match stmts with
      | [] -> ()
      | stmt :: stmts ->
        begin
        if stmt.skind = Label_stmt_core end_l then ()
        else (match stmt with
          | {skind = Assignment_core (_,spec,_)} -> 
            if ExceptionMap.mem fid spec.excep then
              connect fid stmt catch_cfg_node
          | _ -> ());
          process stmts end_l catch_cfg_node fid
        end
  in
  let rec iterate stmts begin_l end_l catch_cfg_node fid =
    match stmts with
      | [] -> ()
      | stmt :: stmts ->
        if (stmt.skind = Label_stmt_core begin_l) then
              process stmts end_l catch_cfg_node fid
        else iterate stmts begin_l end_l catch_cfg_node fid in
  List.iter al stmts;
  ExceptionMap.iter (fun fid labels -> 
    List.iter (fun label ->
      try 
      let catch_cfg_node = Hashtbl.find l2s label.with_label in
        iterate stmts label.from_label label.to_label catch_cfg_node fid
      with Not_found -> Format.eprintf "Undefined label %s.@." label.with_label
    ) labels
  ) emap

(** Fills the [succs] and [preds] fields of [stmts] by adding edges
    corresponding to program order and to goto-s. *)
let stmts_to_cfg (stmts : cfg_node list) emap : unit =
  let l2s = Hashtbl.create 11 in (* maps labels to statements *)
  let al = function
    | {skind = Label_stmt_core l} as s -> Hashtbl.add l2s l s
    | _ -> () in
  let rec process =
    let connect m n = (* adds an edge from [m] to [n] *)
      m.succs <- n :: m.succs; n.preds <- m :: n.preds in
    let find l = (* looks up [l] in [l2s] and reports an error if not found *)
      try Hashtbl.find l2s l
      with Not_found -> Format.eprintf "Undefined label %s.@." l; assert false in
    function
    | {skind = Goto_stmt_core ls} as m :: ss -> 
        List.iter (fun ln -> connect m (find ln)) ls; process ss
    | m :: ((n :: _) as ss)-> connect m n; process ss
    | _ -> () in
  List.iter (fun s -> s.succs <- []; s.preds <- []) stmts;
  List.iter al stmts;
  process stmts;
  exception_cfg stmts emap
 
(* utils for building flowgraphs }}} *)
(* {{{ pretty printing flowgraphs (to .dot) *)

(* stmtsname is a list of programs and names, such that each program's
   cfg is printed in a subgraph with its name.*)
let print_icfg_dotty 
     (stmtsname : (cfg_node list * ((catch_labels list) ExceptionMap.t) * string) list) 
     (filename : string) : unit =
  (* Print an edge between two stmts *)
  let d_cfgedge chan src dest =
    Printf.fprintf chan "\t\t%i -> %i\n" src.sid dest.sid in
  (* Print an exception edge between two stmts *)
  let d_cfg_excep_edge chan src dest =
    Printf.fprintf chan "\t\t%i -> %i\n" src.sid dest.sid in
  (* Print a node and edges to its successors *)
  let d_cfgnode chan (s : cfg_node) =
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      s.sid 
      s.sid 
      (Dot.escape_for_label (Debug.toString pp_stmt_core s.skind));
    List.iter (d_cfgedge chan s) s.succs;
    ExceptionMap.iter (fun excep nodes -> 
      List.iter (d_cfg_excep_edge chan s) nodes
    ) s.esuccs in

  if cfg_debug () then ignore (Printf.printf "\n\nPrinting iCFG as dot file...");
  let chan = open_out (filename ^ ".icfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  List.iter 
    (fun (stmts, catch_clauses, name) -> 
      stmts_to_cfg stmts catch_clauses;
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (Dot.escape_for_label name);
      List.iter (d_cfgnode chan) stmts;
      Printf.fprintf chan  "\t}\n";
    ) 
    stmtsname;
  Printf.fprintf chan  "}\n";
  close_out chan;
  if cfg_debug() then ignore (Printf.printf "\n\n Printing dot file done!")
(* pretty printing flowgraphs (to .dot) }}} *)

(* Print a sequence of core statements to a file *)
let print_core 
    (file: string)
    (mname: string) 
    (stmts : cfg_node list) : unit =

  if core_debug () then ignore (Printf.printf "\n\nPrinting core file for method %s..." mname); 
  
  (* FIXME: Don't understand why I can't use Format.formatter_of_out_channel *)
  Format.pp_set_margin Format.str_formatter 80; 

  let cstr = Format.flush_str_formatter 
     (List.iter (fun x -> pp_stmt_core Format.str_formatter x.skind;
	             Format.pp_print_newline Format.str_formatter () ) stmts) in 

  let chan = open_out (file ^ mname ^ ".core") in 
  Printf.fprintf chan "%s" cstr; 
  close_out chan; 


