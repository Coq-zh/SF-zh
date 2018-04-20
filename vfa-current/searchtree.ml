
type ('a, 'b) prod =
| Pair of 'a * 'b



type key = int

type 'v tree =
| E
| T of 'v tree * key * 'v * 'v tree

(** val empty_tree : 'a1 tree **)

let empty_tree =
  E

(** val lookup : 'a1 -> key -> 'a1 tree -> 'a1 **)

let rec lookup default x = function
| E -> default
| T (tl, k, v, tr) ->
  if (<) x k
  then lookup default x tl
  else if (<) k x then lookup default x tr else v

(** val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let rec insert x v = function
| E -> T (E, x, v, E)
| T (a, y, v', b) ->
  if (<) x y
  then T ((insert x v a), y, v', b)
  else if (<) y x then T (a, y, v', (insert x v b)) else T (a, x, v, b)

(** val elements' :
    'a1 tree -> (key, 'a1) prod list -> (key, 'a1) prod list **)

let rec elements' s base =
  match s with
  | E -> base
  | T (a, k, v, b) -> elements' a ((Pair (k, v))::(elements' b base))

(** val elements : 'a1 tree -> (key, 'a1) prod list **)

let elements s =
  elements' s []
