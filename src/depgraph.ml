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

(** We represent systems of constraints as directed usually-acyclic
    dependency graphs. Most of the program state is captured by a
    stack of these graphs.
*)

open Hashset
open Nfa

(** Constant(s) *)

let def_mapping_size = 50
let def_output_size  = 1000

type nodeid = string 
type state = int
type transition = state * state

(** {6 Language Definitions} *)

(** We use tranition lists to capture multiple alternative solutions
    within a single NFA. This is defined here, but used primarily in
    languageops.ml
*)
let next_transition_list = ref 0

type trans_list_id = int
type trans_list = (trans_list_id * transition list)

let new_trans_list_id () = 
  let cur = !next_transition_list in
    incr next_transition_list;
    cur

let new_trans_list () : trans_list =
  let cur = !next_transition_list in
    incr next_transition_list;
    (cur, [])

(** A submachine represents some part (subset of state space) of one
    or more bigger NFAs. Each such "bigger" NFA is referenced by node
    id, a list of potential start states, and a list of potential
    final states. Separate from that mapping we also store an NFA;
    this matches the language of the node prior to it getting
    submachine status.
*)

type submapping = (nodeid, ((trans_list ref ref) * (trans_list ref ref))) Hashtbl.t
type submachine = nfa * submapping

(** A supermachine represents at least two concatenated submachines,
    separated by sets of epsilon transitions, defined as a pair of
    - the NFA that represents the full set of possible assignments
    - a sequence of triplets of the form:
    - set of 'start' transitions for this submachine
    - node id of this submachine
    - set of 'final' transitions for this submachine

    Adjacent transition sets overlap; for example, for a sequence
    [a;b], the final transition set for a is the start transition set
    for b. We use a shared list representation so that changes to the
    transition sets directly affect all relevant submachines.
*)

type supermapping = (trans_list ref ref) * nodeid * (trans_list ref ref)
type supermachine = nfa *  (supermapping list)

(** A node's language is one of
    - [Unrestricted]: Equivalent to sigmastar
    - [Machine]: A normal NFA
    - [SubMachine]: See {!submachine}
    - [SuperMachine]: See {!supermachine}

    [SubMachine] and [SuperMachine] only used while solving CI-groups; after
    a specific assignment is selected, these are converted to regular NFAs. Legal
    transitions:

   [ Unrestricted -> Machine
     Machine -> SubMachine 
     Machine -> SuperMachine
     SuperMachine -> SubMachine
     SuperMachine, SubMachine -> Machine ]
    
*)
type lang = Unrestricted 
	    | Machine of Nfa.nfa
	    | SubMachine of submachine
	    | SuperMachine of supermachine

(** {6 Dependency Graphs} *)

(** Nodes represent variables and constants; edges represent direct
    dependencies between the nodes. [inedge] Represents the possible
    kinds of inbound edges; [outedge] encodes the corresponding 
    kinds of outbound edges. 

    Note that, for concatenation, we encode the order in the type
    constructors. For example, if node [s1] has an [OutConcatLeft(s2,
    b)] edge, then we have [b alias s1 . s2] and node [s2] will have
    a corresponding edge [OutConcatRight(s1, b)].

*)

type inedge = InConcat  of nodeid * nodeid 
	      | InIsect of nodeid

and outedge = OutConcatLeft of nodeid * nodeid     (* (rhs, target) *)
	      | OutConcatRight of nodeid * nodeid  (* (lhs, target) *)
	      | OutIsect of nodeid

(** Dependency graph node *)
type node = { 
  mutable id   : nodeid;
  mutable lang : lang;
  inb  : inedge hashset;
  outb : outedge hashset
}

type graph = (nodeid, node) Hashtbl.t


(** Add a new node to the specified graph
    @param graph A dependency graph
    @param id Variable name for the new node
    @param lang Language (i.e., an NFA) for new node, or [None]
    @return The new node; [graph] maps [id -> new node]
*)
let new_node (graph : graph)
             (id    : nodeid)
             (lang  : lang) : node =
  let newnode = { id = id;
		  lang = lang;
		  inb  = Hashtbl.create 10;
		  outb = Hashtbl.create 10 } in
    Hashtbl.replace graph id newnode;
    newnode


(** Copy a dependency graph 
    @return A deep copy of [graph]
*)
let copy_graph (graph : graph) : graph = 
  let newgraph = Hashtbl.create (Hashtbl.length graph) in
  let copy_node n = 
    { n with outb = Hashtbl.copy n.outb;
	     inb  = Hashtbl.copy n.inb;
	     lang = match n.lang with 
	       | Machine x -> Machine (Nfa.copy_nfa x) 
	       | SubMachine (m, l) -> SubMachine (Nfa.copy_nfa m, Hashtbl.copy l)
	       | SuperMachine (m, trans) -> SuperMachine (Nfa.copy_nfa m, trans)
	       | Unrestricted -> Unrestricted }
  in
  let copy_mapping id node = 
    Hashtbl.replace newgraph id (copy_node node) 
  in
    Hashtbl.iter copy_mapping graph;
    newgraph

(** @param graph A dependency graph
    @param id The variable name to find
    @return The node associated with [id] in [graph]. A new
    node with [lang=None] is created if no existing binding
    is found.
*)
let find_node (graph : graph)
              (id    : nodeid) : node =
    try Hashtbl.find graph id with
    Not_found -> new_node graph id Unrestricted

(** Pretty print a node's language
    @param graph A dependency graph
    @param id Node id; this node's language will be printed to stdout
*)
let print_lang (graph : graph) (id : nodeid) : unit = 
  Printf.printf "%s gets " id;
  let node = find_node graph id in
  match node.lang with
    | Unrestricted -> Printf.printf "all strings\n"
    | Machine m -> 
	if !Options.elim then elim_dead_states m;
	Nfa.print_nfa (if !Options.minimize then (minimize m) 
		       else m)
    | SubMachine (m,c)-> 
	Printf.printf " SubNfa : \n";
	print_nfa m;
	Hashtbl.iter (fun x _ -> Printf.printf "  - %s\n" x) c
    | SuperMachine (m,_) -> 
	Printf.printf " SuperNfa : \n"; print_nfa m


let printnode (graph : graph) (node : node) : unit = 
  let id = node.id in
  let printedge id edge = match edge with
    | InConcat(x,y) -> Printf.printf "# %s = %s . %s\n" id x y
    | InIsect x     -> Printf.printf "# %s subset %s\n" id x 
  in
    iter (printedge id) node.inb;
    print_lang graph id

(** Pretty print a dependency graph 
    @param graph Dependency graph to print
*)
let print_graph (graph : graph) : unit = 
  let printmaybe id node = 
    if !Options.debug || not (String.get id 0 = '_') then
      printnode graph node
  in
    Hashtbl.iter printmaybe graph

(** Add a concatenation constraint to [graph] ({i L(}[lhs . rhs]{i )}
    subset {i L(}target{i )}). If [lhs], [rhs], or [target] it not
    bound in [graph], then it is created.
    @param graph A dependency graph
    @param lhs The left-hand side of the "constraining" concatenation
    @param rhs The right-hand side of the "constratining" concatenation
    @param target The "constrained" node
*)
let add_concat graph lhs rhs target = 
  let lhs_node = find_node graph lhs in
  let rhs_node = find_node graph rhs in
  let target_node = find_node graph target in
    add lhs_node.outb (OutConcatLeft(rhs, target));
    add rhs_node.outb (OutConcatRight(lhs, target));
    add target_node.inb (InConcat(lhs, rhs))

(** Add a subset constraint to [graph] ({i L(}[target]{i )} subset {i
    L(}[source]{i )}. If either [source] or [target] is not bound in
    [graph], then it is created.
    @param graph A dependency graph
    @param source The "constraining" node
    @param target The "constrained" node
*)
let add_isect (graph : graph)
              (source : nodeid)
              (target : nodeid) : unit =
  let source_node = find_node graph source in
  let target_node = find_node graph target in
    add source_node.outb (OutIsect target);
    add target_node.inb  (InIsect source)

(** Remove an inbound edge from the specified graph. Note: The
    [target] node is created if it did not exist.
    @param graph A dependency graph
    @param target The destination of the [edge] to be removed
    @param edge An inbound edge
*)
let remove_inb (graph : graph)
               (target : nodeid)
               (edge : inedge) : unit =
  let removeout node edge = remove (node.outb) edge in
  let target_node = find_node graph target in
    remove target_node.inb edge;
    match edge with
      | InConcat(a, b) -> 
	  let a_node = find_node graph a in
	  let b_node = find_node graph b in
	    removeout a_node (OutConcatLeft(b, target));
	    removeout b_node (OutConcatRight(a, target))
      | InIsect source -> 
	  let source_node = find_node graph source in
	    remove source_node.outb (OutIsect target)
	
(** Remove an outbound edge from the specified graph. Note: The
    [source] node is created if it did not exist.
    @param graph A dependency graph
    @param source The origin of the [edge] to be removed
    @param edge An outbound edge
*)      
let remove_outb (graph : graph)
                (source : nodeid)
		(edge : outedge) : unit = 
  let removeconcat lhs rhs target =
    let lhs_node = find_node graph lhs in
    let rhs_node = find_node graph rhs in
    let target_node = find_node graph target in
      remove lhs_node.outb (OutConcatLeft(rhs, target));
      remove rhs_node.outb (OutConcatRight(lhs, target));
      remove target_node.inb (InConcat(lhs,rhs))
  in
    match edge with
      | OutConcatLeft (rhs, target) -> removeconcat source rhs target
      | OutConcatRight (lhs, target) -> removeconcat lhs source target
      | OutIsect target ->
	  let source_node = find_node graph source in
	  let target_node = find_node graph target in
	    remove target_node.inb (InIsect source);
	    remove source_node.outb edge

exception Rename 

(** Rename a node, or merge two existing nodes. If [newid] already 
   exists in the given graph, then the nodes are merged by copying
   [curid]'s edges to [newid].
    
    @param graph A dependency graph 
    @param curid The current node name
    @param newid The desired node name 
    @raise Rename If the renaming causes a single node to have two inbound
    concat edge pairs. (Currently caught by the parser and presented
    to the user as an error message.)
*)
let alias_node (graph : graph)
               (curid : nodeid)
               (newid : nodeid) : unit =
  let move_edge orig dest edge =
    remove_inb graph orig edge;
    match edge with
      | InConcat(lhs,rhs) -> add_concat graph lhs rhs dest
      | InIsect(source) -> add_isect graph source dest
  in
  let at_most_one_concat edge acc = match edge with
    | InConcat(_,_) when acc = 1 -> raise Rename
    | InConcat(_,_) -> acc + 1
    | _ -> acc
  in
    if Hashtbl.mem graph newid then
      let curid_node = find_node graph curid in
      let newid_node = find_node graph newid in
	iter (move_edge curid newid) curid_node.inb;
	ignore (fold at_most_one_concat newid_node.inb 0);
	Hashtbl.remove graph curid
    else
      let curid_node = find_node graph curid in
	curid_node.id <- newid;
	Hashtbl.remove graph curid;
	Hashtbl.replace graph newid curid_node

