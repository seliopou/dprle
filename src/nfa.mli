
(* Exposed types *)
type charset = Charset.set
type symbol =
    Character of int
  | Epsilon

type 'a delta   = ('a, ('a, charset) Hashtbl.t) Hashtbl.t
type 'a epsilon = ('a, 'a Hashset.hashset) Hashtbl.t

type state = int
type nfa = {
   	mutable s : state;
   	mutable f : state;
   	mutable delta : state delta;
   	mutable epsilon : state epsilon;
   	mutable q : state Hashset.hashset;
   	mutable next_q : state;
    mutable alpha_size : int
}

module StateSet: Set.S with type elt = state
type stateset = StateSet.t
exception Found_it

(* Constants *)
val def_machine_size : int
val def_delta_size   : int
val def_eps_size     : int

(* Transition Function Operations *)

val all_delta      : ?create:bool -> 'a delta -> 'a -> ('a, charset) Hashtbl.t
val which_symbols  : ?create:bool -> 'a delta -> 'a ->'a -> charset
val which_states   : ?create:bool -> 'a epsilon -> 'a -> 'a Hashset.hashset
val copy_table     : ('a, ('a, 'b) Hashtbl.t) Hashtbl.t ->
                     ('c, ('c, 'b) Hashtbl.t) Hashtbl.t -> ('a -> 'c) -> unit
val copy_set       : ('p, 'p Hashset.hashset) Hashtbl.t ->
                     ('r, 'r Hashset.hashset) Hashtbl.t -> ('p -> 'r) -> unit
val nested_ht_iter : ('a, 'b) Hashtbl.t ->
                     ('c, 'd) Hashtbl.t -> ('a -> 'b -> 'c -> 'd -> unit) -> unit
val fmap           : 'a Hashset.hashset -> ('a -> 'b) -> ('a, 'b) Hashtbl.t

(* NFA Construction *)

val new_nfa_states : ?alpha_size:int -> state -> state -> nfa
val new_state      : nfa -> state
val add_state      : nfa -> state -> unit
val add_trans      : nfa -> state -> symbol -> state -> unit
val add_all_trans  : nfa -> state -> state -> unit
val add_set_trans  : nfa -> state -> charset -> state -> unit
val new_sigmastar  : unit -> nfa

(* NFA Operations *)

val print_nfa          : nfa -> unit
val nfa_to_dot         : nfa -> string
val neighbors          : nfa -> state -> state list
val eps_closure        : nfa -> state -> stateset
val rhs                : nfa -> state -> int -> stateset
val forward_fold_nfa   : (state -> 'a -> 'a) -> nfa -> state -> 'a -> 'a
val backward_mapping   : nfa -> (state, state Hashset.hashset) Hashtbl.t
val backward_reachable : nfa -> state -> state Hashset.hashset
val elim_dead_states   : nfa -> unit
val reverse            : nfa -> nfa
val copy_nfa           : nfa -> nfa
val extract_nfa        : nfa -> state -> state -> nfa
val merge_nfas         : nfa -> nfa -> unit
val normalize_nfa      : nfa -> state -> nfa

(* DFA Operations *)

val nfa_to_dfa : nfa -> nfa
val complement : nfa -> unit
val minimize   : nfa -> nfa

(* Language Operations *)

val concat           : nfa -> nfa -> state Hashset.hashset -> state Hashset.hashset ->
                       (state, state) Hashtbl.t * (state, state) Hashtbl.t * nfa
val simple_concat    : nfa -> nfa -> nfa
val union            : nfa -> nfa -> state Hashset.hashset -> state Hashset.hashset ->
                       ((state, state) Hashtbl.t * (state, state) Hashtbl.t * nfa)
val simple_union     : nfa -> nfa -> nfa
val intersect        : nfa -> nfa ->
                       state Hashset.hashset -> (state, state list) Hashtbl.t * nfa
val simple_intersect : nfa -> nfa -> nfa

val is_empty     : nfa -> bool
val nfa_eq       : nfa -> nfa -> bool
val nfa_subseteq : nfa -> nfa -> bool
val gen_string   : nfa -> string option
