type 'a t 
val add : 'a t -> 'a -> unit
val choose : 'a t -> 'a
val create : int -> 'a t
val elements : 'a t -> 'a list
val iter : ('a -> unit) -> 'a t -> unit
val mem : 'a t -> 'a -> bool
val remove : 'a t -> 'a -> unit
val singleton : 'a -> 'a t