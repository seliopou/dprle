type 'a hashset

val create : int -> 'a hashset

val copy : 'a hashset -> 'a hashset

val clear : 'a hashset -> unit

val mem : 'a hashset -> 'a -> bool

val size : 'a hashset -> int

val empty : 'a hashset -> bool

val iter : ('a -> unit) -> 'a hashset -> unit

val exists : ('a -> bool) -> 'a hashset -> bool

val fold : ('a -> 'b -> 'b) -> 'a hashset -> 'b -> 'b

val filter : ('a -> bool) -> 'a hashset -> 'a list

val split : ('a -> bool) -> 'a hashset -> ('a list * 'a list)

val choose : 'a hashset -> 'a

val add : 'a hashset -> 'a -> unit

val singleton : 'a -> 'a hashset

val to_list : 'a hashset -> 'a list

val from_list : 'a list -> 'a hashset

val remove : 'a hashset -> 'a -> unit

val minus : 'a hashset -> 'a hashset -> 'a hashset

val cup : 'a hashset -> 'a hashset -> 'a hashset

val cap : 'a hashset -> 'a hashset -> 'a hashset

val eq : 'a hashset -> 'a hashset -> bool

val unique : 'a list -> 'a list
