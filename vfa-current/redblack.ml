
type ('a, 'b) prod =
| Pair of 'a * 'b



type key = int

type color =
| Red
| Black

type 'v tree =
| E
| T of color * 'v tree * key * 'v * 'v tree

(** val empty_tree : 'a1 tree **)

let empty_tree =
  E

(** val lookup : 'a1 -> key -> 'a1 tree -> 'a1 **)

let rec lookup default x = function
| E -> default
| T (_, tl, k, v, tr) ->
  if (<) x k
  then lookup default x tl
  else if (<) k x then lookup default x tr else v

(** val balance : color -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let balance rb t1 k vk t2 =
  match rb with
  | Red -> T (Red, t1, k, vk, t2)
  | Black ->
    (match t1 with
     | E ->
       (match t2 with
        | E -> T (Black, t1, k, vk, t2)
        | T (c0, b, y, vy, d) ->
          (match c0 with
           | Red ->
             (match b with
              | E ->
                (match d with
                 | E -> T (Black, t1, k, vk, t2)
                 | T (c1, c, z, vz, d0) ->
                   (match c1 with
                    | Red ->
                      T (Red, (T (Black, t1, k, vk, b)), y, vy, (T (Black, c,
                        z, vz, d0)))
                    | Black -> T (Black, t1, k, vk, t2)))
              | T (c1, b0, y0, vy0, c) ->
                (match c1 with
                 | Red ->
                   T (Red, (T (Black, t1, k, vk, b0)), y0, vy0, (T (Black, c,
                     y, vy, d)))
                 | Black ->
                   (match d with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c2, c3, z, vz, d0) ->
                      (match c2 with
                       | Red ->
                         T (Red, (T (Black, t1, k, vk, b)), y, vy, (T (Black,
                           c3, z, vz, d0)))
                       | Black -> T (Black, t1, k, vk, t2)))))
           | Black -> T (Black, t1, k, vk, t2)))
     | T (c0, a, x, vx, c) ->
       (match c0 with
        | Red ->
          (match a with
           | E ->
             (match c with
              | E ->
                (match t2 with
                 | E -> T (Black, t1, k, vk, t2)
                 | T (c1, b, y, vy, d) ->
                   (match c1 with
                    | Red ->
                      (match b with
                       | E ->
                         (match d with
                          | E -> T (Black, t1, k, vk, t2)
                          | T (c2, c3, z, vz, d0) ->
                            (match c2 with
                             | Red ->
                               T (Red, (T (Black, t1, k, vk, b)), y, vy, (T
                                 (Black, c3, z, vz, d0)))
                             | Black -> T (Black, t1, k, vk, t2)))
                       | T (c2, b0, y0, vy0, c3) ->
                         (match c2 with
                          | Red ->
                            T (Red, (T (Black, t1, k, vk, b0)), y0, vy0, (T
                              (Black, c3, y, vy, d)))
                          | Black ->
                            (match d with
                             | E -> T (Black, t1, k, vk, t2)
                             | T (c4, c5, z, vz, d0) ->
                               (match c4 with
                                | Red ->
                                  T (Red, (T (Black, t1, k, vk, b)), y, vy,
                                    (T (Black, c5, z, vz, d0)))
                                | Black -> T (Black, t1, k, vk, t2)))))
                    | Black -> T (Black, t1, k, vk, t2)))
              | T (c1, b, y, vy, c2) ->
                (match c1 with
                 | Red ->
                   T (Red, (T (Black, a, x, vx, b)), y, vy, (T (Black, c2, k,
                     vk, t2)))
                 | Black ->
                   (match t2 with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c3, b0, y0, vy0, d) ->
                      (match c3 with
                       | Red ->
                         (match b0 with
                          | E ->
                            (match d with
                             | E -> T (Black, t1, k, vk, t2)
                             | T (c4, c5, z, vz, d0) ->
                               (match c4 with
                                | Red ->
                                  T (Red, (T (Black, t1, k, vk, b0)), y0,
                                    vy0, (T (Black, c5, z, vz, d0)))
                                | Black -> T (Black, t1, k, vk, t2)))
                          | T (c4, b1, y1, vy1, c5) ->
                            (match c4 with
                             | Red ->
                               T (Red, (T (Black, t1, k, vk, b1)), y1, vy1,
                                 (T (Black, c5, y0, vy0, d)))
                             | Black ->
                               (match d with
                                | E -> T (Black, t1, k, vk, t2)
                                | T (c6, c7, z, vz, d0) ->
                                  (match c6 with
                                   | Red ->
                                     T (Red, (T (Black, t1, k, vk, b0)), y0,
                                       vy0, (T (Black, c7, z, vz, d0)))
                                   | Black -> T (Black, t1, k, vk, t2)))))
                       | Black -> T (Black, t1, k, vk, t2)))))
           | T (c1, a0, x0, vx0, b) ->
             (match c1 with
              | Red ->
                T (Red, (T (Black, a0, x0, vx0, b)), x, vx, (T (Black, c, k,
                  vk, t2)))
              | Black ->
                (match c with
                 | E ->
                   (match t2 with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c2, b0, y, vy, d) ->
                      (match c2 with
                       | Red ->
                         (match b0 with
                          | E ->
                            (match d with
                             | E -> T (Black, t1, k, vk, t2)
                             | T (c3, c4, z, vz, d0) ->
                               (match c3 with
                                | Red ->
                                  T (Red, (T (Black, t1, k, vk, b0)), y, vy,
                                    (T (Black, c4, z, vz, d0)))
                                | Black -> T (Black, t1, k, vk, t2)))
                          | T (c3, b1, y0, vy0, c4) ->
                            (match c3 with
                             | Red ->
                               T (Red, (T (Black, t1, k, vk, b1)), y0, vy0,
                                 (T (Black, c4, y, vy, d)))
                             | Black ->
                               (match d with
                                | E -> T (Black, t1, k, vk, t2)
                                | T (c5, c6, z, vz, d0) ->
                                  (match c5 with
                                   | Red ->
                                     T (Red, (T (Black, t1, k, vk, b0)), y,
                                       vy, (T (Black, c6, z, vz, d0)))
                                   | Black -> T (Black, t1, k, vk, t2)))))
                       | Black -> T (Black, t1, k, vk, t2)))
                 | T (c2, b0, y, vy, c3) ->
                   (match c2 with
                    | Red ->
                      T (Red, (T (Black, a, x, vx, b0)), y, vy, (T (Black,
                        c3, k, vk, t2)))
                    | Black ->
                      (match t2 with
                       | E -> T (Black, t1, k, vk, t2)
                       | T (c4, b1, y0, vy0, d) ->
                         (match c4 with
                          | Red ->
                            (match b1 with
                             | E ->
                               (match d with
                                | E -> T (Black, t1, k, vk, t2)
                                | T (c5, c6, z, vz, d0) ->
                                  (match c5 with
                                   | Red ->
                                     T (Red, (T (Black, t1, k, vk, b1)), y0,
                                       vy0, (T (Black, c6, z, vz, d0)))
                                   | Black -> T (Black, t1, k, vk, t2)))
                             | T (c5, b2, y1, vy1, c6) ->
                               (match c5 with
                                | Red ->
                                  T (Red, (T (Black, t1, k, vk, b2)), y1,
                                    vy1, (T (Black, c6, y0, vy0, d)))
                                | Black ->
                                  (match d with
                                   | E -> T (Black, t1, k, vk, t2)
                                   | T (c7, c8, z, vz, d0) ->
                                     (match c7 with
                                      | Red ->
                                        T (Red, (T (Black, t1, k, vk, b1)),
                                          y0, vy0, (T (Black, c8, z, vz, d0)))
                                      | Black -> T (Black, t1, k, vk, t2)))))
                          | Black -> T (Black, t1, k, vk, t2)))))))
        | Black ->
          (match t2 with
           | E -> T (Black, t1, k, vk, t2)
           | T (c1, b, y, vy, d) ->
             (match c1 with
              | Red ->
                (match b with
                 | E ->
                   (match d with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c2, c3, z, vz, d0) ->
                      (match c2 with
                       | Red ->
                         T (Red, (T (Black, t1, k, vk, b)), y, vy, (T (Black,
                           c3, z, vz, d0)))
                       | Black -> T (Black, t1, k, vk, t2)))
                 | T (c2, b0, y0, vy0, c3) ->
                   (match c2 with
                    | Red ->
                      T (Red, (T (Black, t1, k, vk, b0)), y0, vy0, (T (Black,
                        c3, y, vy, d)))
                    | Black ->
                      (match d with
                       | E -> T (Black, t1, k, vk, t2)
                       | T (c4, c5, z, vz, d0) ->
                         (match c4 with
                          | Red ->
                            T (Red, (T (Black, t1, k, vk, b)), y, vy, (T
                              (Black, c5, z, vz, d0)))
                          | Black -> T (Black, t1, k, vk, t2)))))
              | Black -> T (Black, t1, k, vk, t2)))))

(** val makeBlack : 'a1 tree -> 'a1 tree **)

let makeBlack = function
| E -> E
| T (_, a, x, vx, b) -> T (Black, a, x, vx, b)

(** val ins : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let rec ins x vx = function
| E -> T (Red, E, x, vx, E)
| T (c, a, y, vy, b) ->
  if (<) x y
  then balance c (ins x vx a) y vy b
  else if (<) y x then balance c a y vy (ins x vx b) else T (c, a, x, vx, b)

(** val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let insert x vx s =
  makeBlack (ins x vx s)

(** val elements' :
    'a1 tree -> (key, 'a1) prod list -> (key, 'a1) prod list **)

let rec elements' s base =
  match s with
  | E -> base
  | T (_, a, k, v, b) -> elements' a ((Pair (k, v))::(elements' b base))

(** val elements : 'a1 tree -> (key, 'a1) prod list **)

let elements s =
  elements' s []
