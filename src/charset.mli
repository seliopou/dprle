type set

val default_set_size : int
exception IllegalChar

(* Utility Functions *)
val valid_char : int -> bool
val char_as_string : int -> string
val string_to_int : string -> int
val digit_list_to_int : string -> int

(* Set Creation *)
val create_empty : unit -> set
val create_full  : int -> set

(* Set Operations *)

val copy  : set -> set
val mem   : set -> int -> bool
val size  : set -> int
val empty : set -> bool
val iter  : (int -> unit) -> set -> unit
val fold  : (int -> 'a -> 'a) -> set -> 'a -> 'a
val add   : set -> int -> unit
val remove : set -> int -> unit
val minus : set -> set -> set
val cup : set -> set -> set
val cap : set -> set -> set
val choose : set -> int
val from_list : int list -> set

(* Pretty printing *)

val print_charset : set -> unit
