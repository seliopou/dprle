(*  Copyright (c) 2008-2009, University of Virginia
    All rights reserved.
   
    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
       * Redistributions of source code must retain the above copyright
         notice, this list of conditions and the following disclaimer.
       * Redistributions in binary form must reproduce the above
         copyright notice, this list of conditions and the following
         disclaimer in the documentation and/or other materials
         provided with the distribution.
       * Neither the name of the University of Virginia nor the names 
         of its contributors may be used to endorse or promote products
         derived from this software without specific prior written
         permission.
   
    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
    (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
    OF THE POSSIBILITY OF SUCH DAMAGE.
   
    Author: Pieter Hooimeijer
*)
open Depgraph
open Solve

type state = Single of graph
	   | Alternatives of graph list 

exception WrongState
exception BadSelectIndex
exception CantAlias
exception BadIdent of string

       
let solverstate : state list ref = ref [ ]

let copy_state s = match s with
  | Single graph -> Single (copy_graph graph)
  | Alternatives gl -> Alternatives (List.map copy_graph gl)

(** @return The current name-to-graph-node bindings
    @raise WrongState If [solverstate] is
    empty, which should never happen (we prevent this elsewhere).
*)
let cur_graph () : graph = 
  match !solverstate with 
    | (Single x)::xs -> x
    | _ -> raise WrongState

let new_node name language =
  ignore (Depgraph.new_node (cur_graph ()) name language)

let intersect sourceid targetid =
    Depgraph.add_isect (cur_graph ()) sourceid targetid

let named_concat lhs rhs target =
  let thenode = Depgraph.find_node (cur_graph ()) target in
  let count = Hashtbl.fold (fun edge _ acc -> match edge with 
			      | InConcat(_,_) -> acc + 1
			      | _ -> acc) thenode.inb 0 in
    if count > 0 then
      raise CantAlias
    else
      Depgraph.add_concat (cur_graph()) lhs rhs target

let anon_concat lhs rhs target =
  new_node target Unrestricted;
  add_concat (cur_graph()) lhs rhs target

(** Clear the entire state (including anything previously saved using
    [!push]. This is done for [reset()] calls in the input, and when
    processing multiple files (unless the [-no-context-reset]
    commandline parameter is set).
*)
let reset_all () =
  solverstate := [ Single (Hashtbl.create def_mapping_size) ]

(** Replace the current environment with [g].  
    @param g The new environment.
    @raise Exception Fails with "Lack of context" if [solverstate] is
    empty, which should never happen (we prevent this elsewhere).
*)
let replace_context (g : graph) : unit =
  match !solverstate with
    | x::xs -> solverstate := (Single g)::xs
    | _ -> failwith "Lack of context"

(** Save the current environment (i.e., push a copy of the current
    dependency graph onto the context stack). This corresponds exactly
    to [push()] in the input language.
    @raise Exception Fails with "Lack of context" if [solverstate] is
    empty, which should never happen (we prevent this elsewhere).
*)
let push () = 
  match !solverstate with
    | x::xs -> solverstate := (copy_state x)::!solverstate
    | _-> failwith "Lack of context."

exception Pop

(** Discard the current environment (i.e., pop the current dependency
    graph off the context stack). This corresponds exactly to [pop()]
    in the input language.  

    @raise Pop if the context stack doesn't contain any previously
    [push]ed environments. 
    @raise Exception Fails with "Shouldn't happen." if there is no
    current environment. This should never happen.
*)
let pop () =
  match !solverstate with
    | [x] -> raise Pop
    | x::xs -> solverstate := xs
    | _ -> failwith "Shouldn't happen."

(** {6 Output Functions} *)

let unsat () = 
  Printf.printf "# Result: Unsatisfiable\n"

let single_sat g =
  Printf.printf "# Result: Single satisfying assignment found\n";
  replace_context g

let many_sat gl = 
  Printf.printf "# Result: %d disjunctive assignments found; use select(n)\n" 
    (List.length gl);
  match !solverstate with
    | x::xs -> solverstate := (Alternatives gl)::xs
    | _ -> failwith "Lack of context"


let bool_yes () =
  Printf.printf "# Result: true\n"

let bool_no () =
  Printf.printf "# Result: false\n"

let inbound_warning (id : nodeid) : unit =
  Printf.printf "# Warning: Node '%s' has inbound constraints;\n" id;
  Printf.printf "#          use solve() or solve_all() to resolve these constraints\n"

let print_node (node : nodeid) : unit =
  let node = try Hashtbl.find (cur_graph ()) node with 
      Not_found -> raise (BadIdent node) in
    Depgraph.printnode (cur_graph ()) node

let print_graph () : unit =
  Depgraph.print_graph (cur_graph ())


let print_strings id x =
  Printf.printf "# { \n";
  Printf.printf "#   '%s'\n" x;
  Printf.printf "# } < L(%s)\n\n" id

let print_no_strings id =
  Printf.printf "\n# { \n";
  Printf.printf "# } < L(%s)\n\n" id

(** {6 Solving} *)
  
let solve linenumber all =
  let solver = if all then solve_all else solve_single in
    match solver (cur_graph ()) with
      | UnSat -> unsat ()
      | Sat [x] -> single_sat x
      | Sat xs  -> many_sat xs

let select n =
  let curalternatives = match !solverstate with
    | (Alternatives gl)::xs -> gl
    | _ -> raise WrongState in
  let desired_graph = try List.nth curalternatives n with _ -> raise BadSelectIndex in
    replace_context desired_graph

let issubset (lhs : nodeid) (rhs : nodeid) : unit =
  let graph = cur_graph () in
  let has_inbound x = Hashtbl.length x.inb > 0 in
  let lhs_node = try Hashtbl.find graph lhs with Not_found -> raise (BadIdent lhs) in
  let rhs_node = try Hashtbl.find graph rhs with Not_found -> raise (BadIdent rhs) in
    if has_inbound lhs_node then
      inbound_warning lhs;
    if has_inbound rhs_node then
      inbound_warning rhs;
  let lhs_lang, rhs_lang = lhs_node.lang, rhs_node.lang in
    if Languageops.lang_subseteq lhs_lang rhs_lang then
      bool_yes ()
    else
      bool_no ()

let areequal (lhs : nodeid) (rhs : nodeid) : unit =
  let graph = cur_graph () in
  let has_inbound x = Hashtbl.length x.inb > 0 in
  let lhs_node = try Hashtbl.find graph lhs with Not_found -> raise (BadIdent lhs) in
  let rhs_node = try Hashtbl.find graph rhs with Not_found -> raise (BadIdent rhs) in
  let lhs_lang, rhs_lang = lhs_node.lang, rhs_node.lang in
    if has_inbound lhs_node then
      inbound_warning lhs;
    if has_inbound rhs_node then
      inbound_warning rhs;
    if Languageops.lang_eq lhs_lang rhs_lang then
      bool_yes ()
    else
      bool_no ()

let all_nodes (graph : graph) : nodeid list =
  let handle_node x _ acc =
      if !Options.debug || not (String.get x 0 = '_') then
	x::acc
      else acc in
    Hashtbl.fold handle_node graph []

let gen_strings (ids : nodeid list) : unit =
  let has_inbound x = Hashtbl.length x.inb > 0 in
  let graph = cur_graph () in

  let ids = match ids with 
    | [] -> all_nodes graph
    | _ -> ids in

  let handle_node id =
    let node = try Hashtbl.find graph id with Not_found -> raise (BadIdent id) in
      if has_inbound node then inbound_warning id;
      match Languageops.gen_strings node.lang with 
	| Some w -> print_strings id w
	| None -> print_no_strings id 
  in
    List.iter handle_node ids
      
let show_machines (nodelist : nodeid list) : unit = match nodelist with
  | [] -> print_graph ()
  | _ -> List.iter (fun x -> print_node x) nodelist
  
