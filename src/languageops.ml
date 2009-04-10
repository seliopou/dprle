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
open Nfa
open Hashset

(** This module defines operations on {!Depgraph.lang}. *)

exception IllegalLangOp of string
exception LangOpFail of string

(** Intersect two languages (used by {!forward_intersect},
    {!group_intersect}, and {!merge_subnfas}.
    
    @param l1 A language
    @param l2 Another language
    @return [l1 cap l2]
    @raise IllegalLangOp if either [l1] or [l2] is a [SuperMachine] or
    a [SubMachine]
*)
let simple_intersect (l1 : lang) (l2 : lang) : lang = match l1, l2 with
  | Unrestricted, Unrestricted -> Unrestricted
  | Machine m, Unrestricted
  | Unrestricted, Machine m -> Machine (Nfa.copy_nfa m)
  | Machine m1, Machine m2 -> Machine (Nfa.simple_intersect m1 m2)
  | _ -> raise (IllegalLangOp "simple_intersect")


(** Language equality

    @param l1 A language
    @param l2 Another language
    @return [l1 ?= l2]
    @raise IllegalLangOp if either [l1] or [l2] is a [SuperMachine] or
    a [SubMachine]
*)
let lang_eq (l1 : lang) (l2 : lang) : bool = match l1, l2 with
  | Unrestricted, Unrestricted -> true
  | Unrestricted, Machine m 
  | Machine m, Unrestricted -> nfa_eq (new_sigmastar ()) m
  | Machine m1, Machine m2 -> nfa_eq m1 m2
  | _ -> raise (IllegalLangOp "lang_eq")


(** Generate strings from a language 
    @param lang The Language
    @return A list of unique strings (length may be less than [n])
*)
let gen_strings (l : lang) : string option = match l with
  | Unrestricted -> Some "a"
  | Machine m -> Nfa.gen_string m
  | _ -> raise (IllegalLangOp "gen_strings")

(** Language subseteq

    @param l1 A language
    @param l2 Another language
    @return [l1 ?subseteq l2]
    @raise IllegalLangOp if either [l1] or [l2] is a [SuperMachine] or
    a [SubMachine]
*)
let lang_subseteq (l1 : lang) (l2 : lang) : bool = match l1, l2 with
  | Unrestricted, Unrestricted -> true
  | Unrestricted, Machine m -> lang_eq Unrestricted (Machine m)
  | Machine m, Unrestricted ->  true
  | Machine m1, Machine m2 -> nfa_subseteq m1 m2
  | _ -> raise (IllegalLangOp "lang_subseteq")


(** {6 Forward solving for non-CI-groups} *)

(** Solve a simple concat constraint
    
    See also: {!group_concat}
    
    @param graph A dependency graph
    @param lhs The node on the left-hand side of the concatenation
    @param rhs The node on the right-hand side of the concatenation
    @param target The node that will hold the result of the concatenation;
    its [lang] element will be updated.
    @raise IllegalLangOp if either [lhs] or [rhs]'s language is a
      [SuperMachine] or [SubMachine]
*)
let forward_concat (graph : graph) 
                   (lhs : nodeid) 
                   (rhs : nodeid) 
                   (target : nodeid) : unit =
  let lhs_node = find_node graph lhs in
  let rhs_node = find_node graph rhs in
  let target_node = find_node graph target in
  let newlang =  match lhs_node.lang, rhs_node.lang with
    | Unrestricted, Unrestricted -> Unrestricted
    | Machine a, Machine b -> Machine (Nfa.simple_concat a b)
    | Unrestricted, Machine b -> Machine (Nfa.simple_concat (new_sigmastar ()) b)
    | Machine a, Unrestricted -> Machine (Nfa.simple_concat a (new_sigmastar ()))
    | _ -> raise (IllegalLangOp "forward_concat")
  in
    target_node.lang <- newlang

(** Solve a simple intersect (i.e., subset) constraint

    See also: {!group_intersect}

    @param graph A dependency graph
    @param source The restricting node
    @param target The to-be-restricted node
    @raise IllegalLangOp If [source] of [target]'s language is a [SuperMachine]
    or [SubMachine] (raised by {!simple_intersect}).
*)
let forward_intersect (graph : graph) (source : nodeid) (target : nodeid) : unit=
  let source_node = find_node graph source in
  let target_node = find_node graph target in
    target_node.lang <- simple_intersect source_node.lang target_node.lang


(** {6 Concat-Intersect Group Operations} *)

(** Given a list of supermapping constraints (i.e., epsilon
    transitions that represent potential solutions), return a flat
    list of all states touching those epsilon transitions.  

    @param l A list of {!Depgraph.supermapping} entries 
    @return A list of states
*)
let ref_flatten (l : supermapping list) : state list =
  let filter_pairs acc (l1,_,l2) = List.rev_append (snd !(!l1))
                                           (List.rev_append (snd !(!l2)) acc) in
  let pairs = List.fold_left filter_pairs [] l in
    List.fold_left (fun acc (x,y) -> x::y::acc) [] pairs


(** Solve a concat constraint in a CI-group

    See also: {!forward_concat}

    The operands (i.e., [lhs] and [rhs]) are converted to submachines,
    while [target] becomes a supermachine. If [lhs] or [rhs] was a
    supermachine, then all its dependent submachines are updated to be
    submachines of [target] instead.
    
    @param graph A dependency graph
    @param lhs Left-hand side of the concatenation
    @param rhs Right-hand side of the concatenation

    @raise IllegalLangOp If the language of one of the operands
    is found to be of the wrong type, or if the target node's
    language is anything other than Unrestricted.
    @raise LangOpFail If the state-in-old-machine to state-in-new-machine
    mappings are not populated correctly (corresponds to [Not_found] in
    the underlying datastructure).
*)
let group_concat (graph : graph) 
                 (lhs : nodeid) 
                 (rhs : nodeid) 
                 (target : nodeid) : unit =
  (* Make lhs and rhs languages look like SuperMachines *)
  let ntl () = ref (ref (new_trans_list ())) in
  let unpack_lang (node : node) : Nfa.nfa * (supermapping list) = 
    match node.lang with
      | Unrestricted -> let m = new_sigmastar () in 
	  node.lang <- Machine m;
	  (m, [( ntl(), node.id, ntl() )])
      | Machine m -> 	  
	  (m, [( ntl(), node.id, ntl() )])
      | SuperMachine (m, trans) -> 
	  (m, trans)
      | SubMachine (m,_) -> 
	  (m, [( ntl(), node.id, ntl() )]) in

  (* get states of interest -- these are states that we
     need to be able to "remember" after we perform the
     concatenation *)
  let get_istates lang = match lang with
    | Machine m
    | SubMachine (m, _) -> [m.s; m.f]
    | SuperMachine (m, trans) -> m.s::m.f::(ref_flatten trans)
    | _ -> raise (IllegalLangOp "group_concat > get_istates")
  in

  let visited : trans_list_id hashset = create 5 in (* TODO: default size  *)
  let visit x = add visited x in
  let visited x = mem visited x in

  (* Convert all epsilon transitions in the given trans_list,
     based on the [state -> state] mapping produced by actually
     performing the concatenation *)
  let convert_trans (l : trans_list ref ref) 
                    (t : (state, state) Hashtbl.t) : unit =
    let conv x = try Hashtbl.find t x with 
	Not_found -> raise (LangOpFail "convert_trans") in
    let conv_trans acc (q1, q2) = (conv q1, conv q2)::acc in
    let id, transitions = fst !(!l), snd !(!l) in
      !l := (id, List.fold_left conv_trans [] transitions) in

  (* Because different nodes may share trans_list instances,
     we must make sure that we only 'update' each instance once *)
  let maybe_convert x mapping = 
    if not (visited (fst !(!x))) then
      (visit (fst !(!x));
       convert_trans x mapping) in

  (* For each operand, convert the appropriate submachine
     mappings to match the states (and node id) of the target *)
  let handle_trans mapping old (lhs_trans, id, rhs_trans) =
    let id_node = find_node graph id in
    let depmap = match id_node.lang with 
      | SubMachine (_, mapping) -> mapping
      | _ -> raise (IllegalLangOp "group_concat > handle_trans") in
      Hashtbl.remove depmap old;
      Hashtbl.replace depmap target (lhs_trans, rhs_trans);
      maybe_convert lhs_trans mapping;
      maybe_convert rhs_trans mapping in

  (* Convert an operand's language to a SubMachine of the target *)
  let machine_to_sub node left right = match node.lang with
    | Machine m 
    | SuperMachine (m,_ ) -> 
	let table = Hashtbl.create 1 in
	  Hashtbl.replace table target (left, right);
	  node.lang <- SubMachine (m,table)
    | SubMachine (_, table) ->
	Hashtbl.replace table target (left,right);
	Hashtbl.remove table lhs;
    | _ -> raise (IllegalLangOp "group_concat > machine_to_sub") in

  let lhs_node    = find_node graph lhs in
  let rhs_node    = find_node graph rhs in
  let target_node = find_node graph target in
  let _ = match target_node.lang with
           | Unrestricted -> ()
           | _ -> raise (IllegalLangOp "group_concat target check")
  in

  let lhs_machine, lhs_trans = unpack_lang lhs_node in
  let rhs_machine, rhs_trans = unpack_lang rhs_node in
  let lhs_istates = from_list (get_istates lhs_node.lang) in
  let rhs_istates = from_list (get_istates rhs_node.lang) in

  (* This is the actual concatenation *) 
  let lhs_map, rhs_map, new_machine = concat lhs_machine rhs_machine
                                             lhs_istates rhs_istates in

  let lhsq x = try Hashtbl.find lhs_map x with _ -> raise (LangOpFail "lhsq") in
  let rhsq x = try Hashtbl.find rhs_map x with _ -> raise (LangOpFail "rhsq") in

  let middle_trans = (new_trans_list_id (), 
		      [ (lhsq lhs_machine.f, rhsq rhs_machine.s) ]) in
  let (lhs_first,_,lhs_last) = try List.hd (List.rev lhs_trans) 
                               with _ -> raise (LangOpFail "lhs_trans") in 
  let (rhs_first,_,rhs_last) = try List.hd rhs_trans 
                               with _ -> raise (LangOpFail "rhs_trans") in
  let new_trans = lhs_trans @ rhs_trans in
    visit (fst middle_trans);
    machine_to_sub lhs_node lhs_first lhs_last;
    machine_to_sub rhs_node rhs_first rhs_last;
    !lhs_last := middle_trans;
    !rhs_first := middle_trans;
    List.iter (handle_trans lhs_map lhs) lhs_trans;
    List.iter (handle_trans rhs_map rhs) rhs_trans;
    target_node.lang <- SuperMachine (new_machine, new_trans)


(** Solve an intersect (i.e., subset) constraint in a CI-group

    See also: {!forward_intersect}

    @param graph A dependency graph
    @param source The restricting node
    @param target The node to be restricted

*)      
let group_intersect (graph : graph) 
                    (source : nodeid) 
		    (target : nodeid) : unit =
  let source_node = find_node graph source in
  let target_node = find_node graph target in
  let source_lang = source_node.lang in
  let target_lang = target_node.lang in

  let (visited : trans_list_id hashset) = create 5 in (* TODO *)
  let visit x = add visited x in
  let visited x = mem visited x in

  let has_epsilon nfa (q1,q2) =
    let table = which_states ~create:false nfa.epsilon q1 in
      mem table q2 
  in

  (* Convert a list of epsilon transitions based on a mapping from
     states to sets of new states. This is similar to what is done
     in group_concat, but the mapping t is now one-to-many rather
     than one-to-one. *) 
  let convert_trans (l : trans_list ref ref) 
                    (t : (state, state list) Hashtbl.t)
		    (nfa : nfa) : unit =
    let conv x = try Some (Hashtbl.find t x) with Not_found -> None in

    let rec list_prod (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
      match l1 with
	| x :: xs -> (List.map (fun y -> (x,y)) l2) @ (list_prod xs l2)
	| _ -> [] in

    let update_entry acc (x,y) = match  (conv x, conv y) with
      | Some x', Some y' -> (list_prod x' y') @ acc
      | _, _ -> acc in
    let updated_list = List.fold_left update_entry [] (snd !(!l)) in
    let updated_list = List.filter (has_epsilon nfa) updated_list in
      !l :=  (fst !(!l), updated_list) in

  let maybe_convert x mapping nfa = 
    if not (visited (fst !(!x))) then
      (visit (fst !(!x));
       convert_trans x mapping nfa) in

  let handle_trans mapping nfa (lhs_trans, id, rhs_trans) =
    maybe_convert lhs_trans mapping nfa;
    maybe_convert rhs_trans mapping nfa in

  let _ = match source_node.lang with
    | Unrestricted
    | Machine _ -> ()
    | SuperMachine _
    | SubMachine _ -> raise (IllegalLangOp "group_intersect source check") in
  
    match source_lang, target_lang with 
      | Unrestricted, _ -> ()
      | _, Unrestricted -> ()
      | Machine m1, Machine m2 -> 
	  target_node.lang <- simple_intersect source_node.lang target_node.lang
      | SuperMachine (ms, trans), Machine mm
      | Machine mm, SuperMachine (ms, trans) ->
	  let istates = from_list (ref_flatten trans) in
	  let mapping, newmachine = intersect ms mm istates in
	    List.iter (handle_trans mapping newmachine) trans;
	    target_node.lang <- SuperMachine (newmachine, trans);
      |  _ -> raise (IllegalLangOp "group_intersect")


(** {6 Converting Processed CI-Groups into Assignments} *)

(** Given a CI-group with [SubMachine] and [SuperMachine] language
    assignments, extract [Machine] assignments for all nodes of
    interest *)

(** An assignment maps each transition list to a single
    transition (i.e., an elemtent in that list). *)
type assignment = (trans_list_id, transition) Hashtbl.t

(** Get the assignment associated with the given transition list
    @param a Assignment mapping
    @param l Transition list
    @param alt Alternative return value if [l] is not mapped in [a]
    @return The value associated with [l] in [a], or a pair [(alt, alt)]
            if [l] not in [l]
*)
let get_assignment (a : assignment) 
                   (l : trans_list ref ref) 
                   (alt : state) : transition =
  let id = fst !(!l) in
    try Hashtbl.find a id with Not_found -> (alt,alt)

(** For a SubMachine dependent on multiple SuperMachines, compute and
    return the intersection of the different subNFAs.

    See also: {!Depgraph.submapping}, {!Depgraph.lang}

    @param graph A dependency graph
    @param a The assignment mapping to use
    @param sub The list of dependencies that define this submachine
    @return The intersected langauge of all sub-NFAs defined by [sub]
            using the given assignment [a]. As a side effect, the
            NFA representation for the supermachines is updated.
    @raise IllegalLangOp If any of the referenced SuperMachines
           have not already been converted to plain old NFAs.
*)
let merge_subnfas (graph : graph) 
                  (a : assignment) 
                  (sub : submapping) : lang =
  let merged_lang = ref Unrestricted in

  let insertnfa outer (qs', qs) inner (qf, qf') =
    let offset = outer.next_q in
    let convert x = x + offset in
    let epss = which_states ~create:false outer.epsilon qs' in
    let epss2 = which_states ~create:false outer.epsilon qf in
      Hashset.remove epss  qs;
      Hashset.remove epss2 qf';
      merge_nfas outer inner;
      add_trans outer qs' Epsilon (convert inner.s);
      add_trans outer (convert inner.f) Epsilon qf' in

  let intersect_step id (lhs, rhs) = 
    let id_node = find_node graph id in
    let machine = match id_node.lang with
      | Machine m -> m
      | _ -> failwith "Encountered inconsistent depgraph state." in
    let q_l', q_l = get_assignment a lhs machine.s in
    let q_r, q_r' = get_assignment a rhs machine.f in
    let submachine = extract_nfa machine q_l q_r in
      merged_lang := simple_intersect (Machine submachine) (!merged_lang) in 

  let merge_step id (lhs, rhs) =
    let id_node = find_node graph id in
    let machine = match id_node.lang with
      | Machine m -> m
      | _ -> failwith "Encountered inconsistent depgraph state." in
    let qs', qs = get_assignment a lhs machine.s in
    let qf, qf' = get_assignment a rhs machine.f in
    let othermachine = match !merged_lang with
      | Machine m -> m
      | _ -> failwith "Shouldn't happen." 
    in
      insertnfa machine (qs', qs) othermachine (qf, qf') 
  in

    Hashtbl.iter intersect_step sub;
    Hashtbl.iter merge_step sub;
    !merged_lang

(** Solving a CI-group ends with the creation of zero or more 
    copies of the dependency graph. This is where we turn 
    [Super]- and [SubMachines] back into normal NFAs.

    @param assgn Satisfying assignment to generate
    @param group A subset of graph nodes that makes up a
                 (fully processed) CI-group 
    @param curgraph A dependency graph
    @return A copy of [curgraph] containing the requested
            satisfying assignment for [group]
    @raise IllegalLangOp If something bad happened
*)
let create_graph (assgn : assignment)
                 (group : nodeid hashset)
                 (curgraph : graph) : graph =

  let new_graph = copy_graph curgraph in
  let visited = create (size group) in
  let mem_visited x = mem visited (fst !(!x)) in
  let add_visited x = add visited (fst !(!x)) in

  let remove_epsilon nfa (lstate,rstate) =
    let theset = which_states ~create:false nfa.epsilon lstate in
      remove theset rstate in

  (* Remove epsilon transitions that represent other satisfying assignments *)
  let remove_epsilon_step id =
    let id_node = find_node new_graph id in
    let machine, trans = match id_node.lang with
      | SuperMachine (m, trans) -> (m,trans)
      | _ -> raise (IllegalLangOp "create_graph > remove_epsilon_step") in
    
    let handle_constraint (lhs, id, rhs) = 
      if not (mem_visited lhs) then (
	let (l, r) = get_assignment assgn lhs machine.s in
	  List.iter (remove_epsilon machine) (snd !(!lhs));
	  add_trans machine l Epsilon r;
	  add_visited lhs);
      if not (mem_visited rhs) then (
	let (l, r) = get_assignment assgn rhs machine.f in
	  List.iter (remove_epsilon machine) (snd !(!rhs));
	  add_trans machine l Epsilon r;
	  add_visited rhs)
    in
      id_node.lang <- Machine machine;
      List.iter handle_constraint trans
  in

  (* for any submachines that depend on more than one supermachine, we
     need to update both the submachine and all of the associated
     supermachines *)
  let merge_overlap_step id =
    let id_node = find_node new_graph id in
      
    let constraints = match id_node.lang with 
      | SubMachine (_, c) -> c
      | _ -> raise (IllegalLangOp "create_graph > merge_overlap_step")
    in
      if Hashtbl.length constraints > 1 then
	id_node.lang <- (merge_subnfas new_graph assgn constraints)
      else
	let set_lang super (lhs, rhs) =
	  let super_node = find_node new_graph super in
	  let machine = match super_node.lang with
	    | Machine m -> m
	    | _ -> raise (IllegalLangOp "create_graph > merge_overlap_step") in

	  let s', s = get_assignment assgn lhs machine.s in
	  let f, f' = get_assignment assgn rhs machine.f in
	    id_node.lang <- Machine (extract_nfa machine s f)
	in
	  Hashtbl.iter set_lang constraints in
  
  let bottom_pred id = 
    let id_node = find_node new_graph id in
    let edge_pred edge = match edge with
      | OutConcatLeft _
      | OutConcatRight _ -> true
      | OutIsect target -> mem group target 
    in
      not (exists edge_pred id_node.outb) 
  in

  let supernodes, subnodes = split bottom_pred group in
    List.iter remove_epsilon_step supernodes;
    List.iter merge_overlap_step  subnodes;
    new_graph
