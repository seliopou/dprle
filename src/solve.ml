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

open Languageops
open Depgraph
open Hashset
open Nfa

(** This module contains the bulk of the solving code. At a high
    level, the {!Languageops} module implements the individual solving
    steps, while this module determines the order in which to apply
    those steps.
*)

(** {6 Querying Dependency Graphs} *)

(** [true] if [n] has no inbound edges *)
let free (n : node) : bool = 
  Hashtbl.length (n.inb) == 0

(** [true] if [n] has at least one outbound edge *)
let not_done (n : node) : bool=
  Hashtbl.length n.outb > 0

(** [true] if [n] has either (1) any number of inbound intersect edges
    and no inbound concat edges; or (2) a single inbound concat edge and no
    inbound intersect edges
*)
let almostfree (n : node) : bool = 
  fold (fun edge acc -> match edge with
	  | InIsect e -> acc && true
	  | InConcat(_,_) -> (size n.inb = 1)
       ) n.inb true

(** Find all nodes that are both [free] and [not_done]. *)
let free_not_done_nodes (graph : graph) : nodeid Hashset.hashset = 
  let result = create (Hashtbl.length graph) in
    Hashtbl.iter (fun _ node -> 
		    if (free node && not_done node) then
		      add result node.id
		 ) graph;
    result

(** Number of nodes with outbound edges remaining *)
let done_count (graph : graph) : int = 
  let count_step _ x acc = acc + (if not_done x then 0 else 1) in
    Hashtbl.fold count_step graph 0

(** Does [graph] require further processing? *)
let has_work_left (graph : graph) : bool =
  done_count graph < (Hashtbl.length graph)

(** Does this graph contain zero empty language assignments? 
    @raise IllegalLangOp if we encounter [Super] or [SubMachine] assignments
*)
let is_satisfying (graph : graph) : bool = 
  let non_empty _ node acc = acc && match node.lang with
    | Unrestricted -> true
    | Machine m -> not (is_empty m)
    | _ -> raise (IllegalLangOp "is_satisfying")
  in
    Hashtbl.fold non_empty graph true

(** Check whether it is safe to forward-process an outbound edge. If
    the 'owner' of the outbound edge is free and [is_simple_forward
    edge] returns [true], then it is sufficient to perform the
    corresponding concatenation or language intersection and eliminate
    the edge.

    If [is_simple_forward edge] returns [false], then either the 
    other operand is unavailable (in the case of a concat), and/or
    the current node is part of a concat-intersect group and
    thus requires special handling.
*)
let is_simple_forward (graph : graph)
                      (edge : outedge) : bool = 
  match edge with
    | OutConcatLeft(other, target)
    | OutConcatRight(other, target) -> 
	let other_node  = find_node graph other in
	let target_node = find_node graph target in
	  free other_node && almostfree target_node
    | OutIsect target -> 
	let target_node = find_node graph target in
	  almostfree target_node

exception Done_finding

(** Find a CI-group that is ready for processing (i.e., doesn't have any inbound
    edges from non-free nodes). 

    @return A tuple containing the CI-group itself and the set of nodes with
    inbound edges to the group, or [None] if the [graph] does not contain any
    free CI-groups.
*)
let find_free_group (graph : graph) : (string hashset * string hashset) option =
  let not_visited = Hashset.create (Hashtbl.length graph) in
  let _           = Hashtbl.iter (fun x _ -> add not_visited x) graph in
  let cur_group   = Hashset.create (Hashtbl.length graph) in
  let cur_inbound = Hashset.create (Hashtbl.length graph) in

  let is_in_isect x = match x with
    | InIsect _ -> true
    | _ -> false in
  let is_in_concat x = match x with
    | InConcat (_,_) -> true
    | _ -> false in
  let bad_edge edge = match edge with
    | InIsect source -> 
        let source_node = find_node graph source in
          not (free source_node)
    | _ -> false in

  let queueadd = ref [] in
  let enqueue_out edge = match edge with
    | OutConcatLeft  (rhs,target) -> queueadd := (target,false)::!queueadd
    | OutConcatRight (lhs,target) -> queueadd := (target,false)::!queueadd
    | OutIsect target -> () in
  let enqueue_in edge = match edge with 
    | InConcat (lhs, rhs) -> () (* do nothing *)
    | InIsect source -> add cur_inbound source in
  let enqueue_in_backw edge = match edge with
    | InConcat (lhs, rhs) -> queueadd := (lhs,true)::(rhs, true)::!queueadd
    | _ -> () (* do nothing *) in

  let visit x   = remove not_visited x in
  let visited x = not (mem not_visited x) in

  let rec walk (queue : (string * bool) list) : bool = match queue with
    | (cur,backw)::qs ->
        if visited cur then walk qs else enqueue_neighbors cur backw queue
    | _ -> size cur_group > 1
  and enqueue_neighbors cur backw queue : bool =
    let cur_node = find_node graph cur in
    let any_nonfree = exists bad_edge cur_node.inb in
      if any_nonfree then
        (clear cur_group;
         clear cur_inbound;
         false)
      else begin
        visit cur; add cur_group cur;
        (* If we are going backwards already or if the current node
           has an intersect constraint, and if the current node has an
           inbound concatenation constraint, then add the operands of
           that concatenation. Note that we assume at most one inbound
           concat constraint per node; we enforce this elsewhere. *)
        if backw || (exists is_in_isect cur_node.inb) then
          (match filter is_in_concat cur_node.inb with
             | edge::nothing -> enqueue_in_backw edge
             | _ -> ()); (* nothing *)
        iter enqueue_out cur_node.outb;
        iter enqueue_in  cur_node.inb;
        let toadd = List.filter (fun (x,_) -> not (visited x)) !queueadd in
        let newqueue = (List.tl queue) @ toadd in
          walk newqueue
      end
  in
  let consider_node id id_node =
    if not (visited id) && (exists is_in_isect id_node.inb) &&
      (exists is_in_concat id_node.inb) then
        if (walk [ (id, false) ]) then raise Done_finding
  in
    try
      Hashtbl.iter consider_node graph;
      None (* No groups found *)
    with Done_finding -> 
      Some (cur_group, cur_inbound) (* Group found *)
     
(** {6 Solving} *)


(** Solve all the simple (non-CI-group) outbound constraints imposed
    by node [id].  Processed edges are removed from the [graph], and
    the affected nodes may have their language updated. See also:
    {!is_simple_forward}.

    @param graph Graph to process
    @param id Node to process outbound constraints for
*)
let solve_single_forward (graph : graph) (id : string) : unit =
  let id_node = find_node graph id in
  let processedge edge = 
    remove_outb graph id edge;
    match edge with
      | OutConcatLeft(rhs, target)  -> forward_concat graph id rhs target
      | OutConcatRight(lhs, target) -> forward_concat graph lhs id target
      | OutIsect target             -> forward_intersect graph id target
  in
  let processmaybe edge = if is_simple_forward graph edge then processedge edge in
    Hashset.iter processmaybe id_node.outb

(** Solve simple (non-CI-group) constraints for all nodes in [graph]
    that are free. The main algorithm alternates calls to this
    function with those to {!solve_group}.
    @param graph A dependency graph

*)
let solve_forward (graph : graph) : unit = 
  let curset = free_not_done_nodes graph in
    Hashset.iter (solve_single_forward graph) curset


(** Eagerly enumerate all combinations of elements in some number of
    lists. Used by {!enumerate_solutions}
    @param set A hashset of lists 
    @return A list of ['a list -> 'a] mappings; each mapping
    represents one combination. For example, given input [ \{ [1,2],[3]
    \}], [enumerate] returns a list of two mappings: [ [ \{ [1,2] -> 1,
    [3] -> 3 \}, \{ [1,2] -> 2, [3] -> 3\} ] ]
*)
let enumerate (set : trans_list hashset) : ((int, transition) Hashtbl.t) list =
  let rec listprod lhs (id, rhs) = match lhs with
    | x::xs -> 
        (List.map (fun y -> 
		     let cur = Hashtbl.copy x in
                       Hashtbl.replace cur id y; 
		       cur
		  ) rhs)
        @ (listprod xs (id, rhs))
    | _ -> []
  in
  (* first iteration creates new mappings; subsequent iterations
     populate them further.  *)
  let prod lhs (id, rhs) = match lhs with
    | x::xs -> listprod lhs (id, rhs)
    | [] -> List.map (fun y -> 
		       let cur = Hashtbl.create (List.length rhs) in
                         Hashtbl.replace cur id y; cur
                    ) rhs
  in
   fold (fun (id, curlist) acc -> prod acc (id, curlist)) set []

(** Eagerly enumerate all solutions for a given CI-group.
    @param group The CI-group currently under consideration
    @param graph A dependency graph

*)
let enumerate_solutions (group : nodeid hashset)
                        (graph : graph) : graph list =
  let constraintset = create (size group) in
  let visited = create (size group) in
  let visit x = add visited (fst !(!x));
		add constraintset !(!x) in
  let visited x = mem visited (fst !(!x)) in

  let visit_constraint (lhs, id, rhs) =
    if not (visited lhs) then visit lhs;
    if not (visited rhs) then visit rhs in

  let visit_node id =
    let id_node = find_node graph id in match id_node.lang with
      | SuperMachine (m, trans) -> 
	  List.iter visit_constraint trans
      | _ -> () in

  let process_combination assign = 
    create_graph assign group graph in

    iter visit_node group;

    let constraintset = from_list 
      (filter (fun (x,y) -> List.length y > 0) constraintset) in
    let possibilities = enumerate constraintset in

    let not_empty graph = 
      let has_empty_lang n = 
	let pred_node = find_node graph n in
          match pred_node.lang with
            | Machine x    -> Nfa.is_empty x 		  
            | _ -> (Printf.printf "arp;" ; false)
      in
	fold (fun x acc -> (not (has_empty_lang x)) && acc) group true
    in
       List.fold_left (fun acc x -> 
			 let graph = process_combination x in
			   if not_empty graph then
			     (graph::acc )
			   else
			     (acc)
		      ) [] possibilities

(** Check each solution for nodes that have been assigned the empty
    language; return only those that have a non-empty assignment for
    each node.

*)
let filter_solutions (group : string hashset)
    (graphlist : graph list) : graph list = 
  
  let not_empty graph = 
    let has_empty_lang n = 
      let pred_node = find_node graph n in
        match pred_node.lang with
          | Machine x    -> if Nfa.is_empty x then 
	      (true) else false
		
          | _ -> false
    in
      not (exists has_empty_lang group)

  in
    List.filter not_empty graphlist

(** Remove the edges associated with a CI-group.
    @param group A CI-group
    @param inbound The set of nodes that are not part of the
                   CI-group, but have outbound intersect-edges
                   into [group]
    @param graph The dependency graph
*)
let fix_edges (group : string hashset) 
              (inbound : string hashset)
              (graph : graph) : unit =
  let remove_inbound edge = match edge with 
    | OutIsect n -> mem group n
    | _ -> false in
  let remove_group edge = match edge with 
    | OutIsect _ -> false
    | OutConcatLeft (rhs, target) -> mem group target
    | OutConcatRight (lhs, target) -> mem group target in
  let group_it id = 
    let id_node = find_node graph id in 
      iter (fun edge -> if remove_group edge then
              remove_outb graph id edge) id_node.outb 
  in let inbound_it id = 
    let id_node = find_node graph id in
      iter (fun edge -> if remove_inbound edge then 
              remove_outb graph id edge) id_node.outb
  in
    iter group_it group;
    iter inbound_it inbound

      
(** (Eagerly) find statisfying assignments for a single CI-group. The last
    two parameters come from a call to {!find_free_group}.

    @param graph The current dependency graph. May be modified in
    place.
    @param group A CI-group ready for solving (i.e., all nodes with
    outbound edges into the group are free).
    @param inbound The set of nodes in the graph that constrain one or
    more edges in the group itself (at present always through
    intersect edges).
    @return A list of alternative solutions for the CI-group (contains 0
    elements if no satisfying assignment exists). The edge structure
    of each returned graph is the same; only the language assignments
    for nodes in [group] differs.
*)
let solve_group (graph : graph)
                (group : string hashset)
                (inbound : string hashset) : graph list =

  let is_top_node id = 
    let id_node = find_node graph id in
    let edge_from_group edge = match edge with
      | InConcat (a,b) -> mem group a || mem group b
      | InIsect (a) -> mem group a 
    in
      not (exists edge_from_group id_node.inb) in

  let group_copy = copy group in
  let visited = create (Hashtbl.length group) in 
  let visit x = add visited x; remove group x in
  let visited x = mem visited x in

  let eliminate_top id = 
    let id_node = find_node graph id in 
    let perform_intersect edge = match edge with
      | InIsect source -> group_intersect graph source id
      | _ -> () in
    let perform_concat edge = match edge with
      | OutConcatRight(lhs, target) when visited lhs -> 
	  group_concat graph lhs id target
      | OutConcatLeft(rhs, target) when visited rhs -> 
	  group_concat graph id rhs target
      | _ -> () 
    in
      iter perform_intersect id_node.inb;
      iter perform_concat id_node.outb;
      visit id in 

  let rec walk () = 
    let topnodes = filter (fun x -> 
			     is_top_node x && not (visited x)
			  ) group  in
      List.iter eliminate_top topnodes;
      if Hashtbl.length group = 0 then ()
      else walk () in

  let _ = walk () in
  let solutions = enumerate_solutions group_copy graph in

  let solutions = filter_solutions group_copy solutions in
    fix_edges group_copy inbound graph;
    List.iter (fix_edges group_copy inbound) solutions;
    solutions

(** Solve the constraint system *)

type outcome = UnSat
	       | Sat of graph list

let solve_step graph = 
  solve_forward graph;
  match (find_free_group graph) with
    | None -> [ graph ]
    | Some (group, inbounds) -> solve_group graph group inbounds

let solve_single (graph : graph) : outcome = 
  let rec walk queue = match queue with
    | [] -> UnSat
    | q::qs when not (has_work_left q) && is_satisfying q -> Sat [q]
    | q::qs when not (has_work_left q) -> walk qs
    | q::qs -> walk (qs @ (solve_step q)) 
  in
    walk [graph]

let solve_all (graph : graph) : outcome = 
  let add oc g = match oc with
    | UnSat -> Sat [g]
    | Sat gl -> Sat (g::gl) in

  let rec walk_all queue sol = match queue with
    | [] -> sol
    | q::qs when not (has_work_left q) && is_satisfying q -> walk_all qs (add sol q)
    | q::qs when not (has_work_left q) -> walk_all qs sol
    | q::qs -> walk_all (qs @ (solve_step q)) sol
  in
    walk_all [graph] UnSat
