
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = ( + )
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> n0)
    (fun k ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> n0)
      (fun l -> sub k l)
      m)
    n0

(** val eqb : int -> int -> bool **)

let rec eqb = ( = )

(** val leb : int -> int -> bool **)

let rec leb n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n0

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n0 m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n0

  (** val leb : int -> int -> bool **)

  let rec leb n0 m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n0
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x ((fun x -> x + 1) 0)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val to_nat : n -> int **)

  let to_nat = function
  | N0 -> 0
  | Npos p -> Pos.to_nat p
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val eqb_string : char list -> char list -> bool **)

let eqb_string x y =
  if string_dec x y then true else false

type 'a total_map = char list -> 'a

(** val t_empty : 'a1 -> 'a1 total_map **)

let t_empty v _ =
  v

(** val t_update : 'a1 total_map -> char list -> 'a1 -> char list -> 'a1 **)

let t_update m x v x' =
  if eqb_string x x' then v else m x'

type state = int total_map

type aexp =
| ANum of int
| AId of char list
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BLe of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

(** val aeval : state -> aexp -> int **)

let rec aeval st = function
| ANum n0 -> n0
| AId x -> st x
| APlus (a1, a2) -> add (aeval st a1) (aeval st a2)
| AMinus (a1, a2) -> sub (aeval st a1) (aeval st a2)
| AMult (a1, a2) -> mul (aeval st a1) (aeval st a2)

(** val beval : state -> bexp -> bool **)

let rec beval st = function
| BTrue -> true
| BFalse -> false
| BEq (a1, a2) -> eqb (aeval st a1) (aeval st a2)
| BLe (a1, a2) -> leb (aeval st a1) (aeval st a2)
| BNot b1 -> negb (beval st b1)
| BAnd (b1, b2) -> (&&) (beval st b1) (beval st b2)

(** val empty_st : int total_map **)

let empty_st =
  t_empty 0

type com =
| CSkip
| CAss of char list * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

(** val ceval_step : state -> com -> int -> state option **)

let rec ceval_step st c i =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> None)
    (fun i' ->
    match c with
    | CSkip -> Some st
    | CAss (l, a1) -> Some (t_update st l (aeval st a1))
    | CSeq (c1, c2) ->
      (match ceval_step st c1 i' with
       | Some st' -> ceval_step st' c2 i'
       | None -> None)
    | CIf (b, c1, c2) ->
      if beval st b then ceval_step st c1 i' else ceval_step st c2 i'
    | CWhile (b1, c1) ->
      if beval st b1
      then (match ceval_step st c1 i' with
            | Some st' -> ceval_step st' c i'
            | None -> None)
      else Some st)
    i

(** val isWhite : char -> bool **)

let isWhite c =
  let n0 = nat_of_ascii c in
  (||)
    ((||)
      (Nat.eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))))
      (Nat.eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))))
    ((||)
      (Nat.eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))
      (Nat.eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))

(** val isLowerAlpha : char -> bool **)

let isLowerAlpha c =
  let n0 = nat_of_ascii c in
  (&&)
    (Nat.leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      n0)
    (Nat.leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isAlpha : char -> bool **)

let isAlpha c =
  let n0 = nat_of_ascii c in
  (||)
    ((&&)
      (Nat.leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n0)
      (Nat.leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (Nat.leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1)
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n0)
      (Nat.leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isDigit : char -> bool **)

let isDigit c =
  let n0 = nat_of_ascii c in
  (&&)
    (Nat.leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))))))))))))))))))) n0)
    (Nat.leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type chartype =
| White
| Alpha
| Digit
| Other

(** val classifyChar : char -> chartype **)

let classifyChar c =
  if isWhite c
  then White
  else if isAlpha c then Alpha else if isDigit c then Digit else Other

(** val list_of_string : char list -> char list **)

let rec list_of_string = function
| [] -> []
| c::s0 -> c :: (list_of_string s0)

(** val string_of_list : char list -> char list **)

let rec string_of_list xs =
  fold_right (fun x x0 -> x::x0) [] xs

type token = char list

(** val tokenize_helper :
    chartype -> char list -> char list -> char list list **)

let rec tokenize_helper cls acc xs =
  let tk = match acc with
           | [] -> []
           | _ :: _ -> (rev acc) :: [] in
  (match xs with
   | [] -> tk
   | x :: xs' ->
     (match cls with
      | White ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x
         | x0 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs'))
             x)
      | Alpha ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Alpha ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Alpha (x :: acc) xs'
                  else if b1
                       then tokenize_helper Alpha (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Alpha (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Alpha
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Alpha
                                                       (x :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Alpha (x :: acc)
                                             xs'
                            else tokenize_helper Alpha (x :: acc) xs'
             else if b0
                  then tokenize_helper Alpha (x :: acc) xs'
                  else if b1
                       then tokenize_helper Alpha (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Alpha (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Alpha
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Alpha
                                                       (x :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Alpha (x :: acc)
                                             xs'
                            else tokenize_helper Alpha (x :: acc) xs')
             x
         | Digit ->
           let tp = Digit in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x)
      | Digit ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Alpha ->
           let tp = Alpha in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x
         | Digit ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Digit (x :: acc) xs'
                  else if b1
                       then tokenize_helper Digit (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Digit (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Digit
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Digit
                                                       (x :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Digit (x :: acc)
                                             xs'
                            else tokenize_helper Digit (x :: acc) xs'
             else if b0
                  then tokenize_helper Digit (x :: acc) xs'
                  else if b1
                       then tokenize_helper Digit (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Digit (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Digit
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Digit
                                                       (x :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Digit (x :: acc)
                                             xs'
                            else tokenize_helper Digit (x :: acc) xs')
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x)
      | Other ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Other ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Other (x :: acc) xs'
                  else if b1
                       then tokenize_helper Other (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Other (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Other
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Other
                                                       (x :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Other (x :: acc)
                                             xs'
                            else tokenize_helper Other (x :: acc) xs'
             else if b0
                  then tokenize_helper Other (x :: acc) xs'
                  else if b1
                       then tokenize_helper Other (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Other (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Other
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Other
                                                       (x :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Other (x :: acc)
                                             xs'
                            else tokenize_helper Other (x :: acc) xs')
             x
         | x0 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs'))
             x)))

(** val tokenize : char list -> char list list **)

let tokenize s =
  map string_of_list (tokenize_helper White [] (list_of_string s))

type 'x optionE =
| SomeE of 'x
| NoneE of char list

type 't parser0 = token list -> ('t * token list) optionE

(** val many_helper :
    'a1 parser0 -> 'a1 list -> int -> token list -> ('a1 list * token list)
    optionE **)

let rec many_helper p acc steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match p xs with
    | SomeE x -> let (t, xs') = x in many_helper p (t :: acc) steps' xs'
    | NoneE _ -> SomeE ((rev acc), xs))
    steps

(** val many : 'a1 parser0 -> int -> 'a1 list parser0 **)

let rec many p steps =
  many_helper p [] steps

(** val firstExpect : token -> 'a1 parser0 -> 'a1 parser0 **)

let firstExpect t p = function
| [] ->
  NoneE
    (append
      ('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('\''::[]))))))))))
      (append t ('\''::('.'::[]))))
| x :: xs' ->
  if string_dec x t
  then p xs'
  else NoneE
         (append
           ('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('\''::[]))))))))))
           (append t ('\''::('.'::[]))))

(** val expect : token -> unit parser0 **)

let expect t =
  firstExpect t (fun xs -> SomeE ((), xs))

(** val parseIdentifier : token list -> (char list * token list) optionE **)

let parseIdentifier = function
| [] ->
  NoneE
    ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('i'::('d'::('e'::('n'::('t'::('i'::('f'::('i'::('e'::('r'::[])))))))))))))))))))
| x :: xs' ->
  if forallb isLowerAlpha (list_of_string x)
  then SomeE (x, xs')
  else NoneE
         (append
           ('I'::('l'::('l'::('e'::('g'::('a'::('l'::(' '::('i'::('d'::('e'::('n'::('t'::('i'::('f'::('i'::('e'::('r'::(':'::('\''::[]))))))))))))))))))))
           (append x ('\''::[])))

(** val parseNumber : token list -> (int * token list) optionE **)

let parseNumber = function
| [] ->
  NoneE
    ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::[])))))))))))))))
| x :: xs' ->
  if forallb isDigit (list_of_string x)
  then SomeE
         ((fold_left (fun n0 d ->
            add
              (mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) 0)))))))))) n0)
              (sub (nat_of_ascii d) (nat_of_ascii '0'))) (list_of_string x) 0),
         xs')
  else NoneE
         ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::[])))))))))))))))

(** val parsePrimaryExp : int -> token list -> (aexp * token list) optionE **)

let rec parsePrimaryExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseIdentifier xs with
    | SomeE x -> let (i, rest) = x in SomeE ((AId i), rest)
    | NoneE _ ->
      (match parseNumber xs with
       | SomeE x -> let (n0, rest) = x in SomeE ((ANum n0), rest)
       | NoneE _ ->
         (match firstExpect ('('::[]) (parseSumExp steps') xs with
          | SomeE x ->
            let (e, rest) = x in
            (match expect (')'::[]) rest with
             | SomeE x0 -> let (_, rest') = x0 in SomeE (e, rest')
             | NoneE err -> NoneE err)
          | NoneE err -> NoneE err)))
    steps

(** val parseProductExp : int -> token list -> (aexp * token list) optionE **)

and parseProductExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parsePrimaryExp steps' xs with
    | SomeE x ->
      let (e, rest) = x in
      (match many (firstExpect ('*'::[]) (parsePrimaryExp steps')) steps' rest with
       | SomeE x0 ->
         let (es, rest') = x0 in
         SomeE ((fold_left (fun x1 x2 -> AMult (x1, x2)) es e), rest')
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseSumExp : int -> token list -> (aexp * token list) optionE **)

and parseSumExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseProductExp steps' xs with
    | SomeE x ->
      let (e, rest) = x in
      (match many (fun xs0 ->
               match firstExpect ('+'::[]) (parseProductExp steps') xs0 with
               | SomeE x0 -> let (e0, rest') = x0 in SomeE ((true, e0), rest')
               | NoneE _ ->
                 (match firstExpect ('-'::[]) (parseProductExp steps') xs0 with
                  | SomeE x0 ->
                    let (e0, rest') = x0 in SomeE ((false, e0), rest')
                  | NoneE err -> NoneE err)) steps' rest with
       | SomeE x0 ->
         let (es, rest') = x0 in
         SomeE
         ((fold_left (fun e0 term ->
            let (y, e1) = term in
            if y then APlus (e0, e1) else AMinus (e0, e1)) es e), rest')
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseAExp : int -> token list -> (aexp * token list) optionE **)

let parseAExp =
  parseSumExp

(** val parseAtomicExp : int -> token list -> (bexp * token list) optionE **)

let rec parseAtomicExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match expect ('t'::('r'::('u'::('e'::[])))) xs with
    | SomeE x -> let (_, rest) = x in SomeE (BTrue, rest)
    | NoneE _ ->
      (match expect ('f'::('a'::('l'::('s'::('e'::[]))))) xs with
       | SomeE x -> let (_, rest) = x in SomeE (BFalse, rest)
       | NoneE _ ->
         (match firstExpect ('~'::[]) (parseAtomicExp steps') xs with
          | SomeE x -> let (e, rest) = x in SomeE ((BNot e), rest)
          | NoneE _ ->
            (match firstExpect ('('::[]) (parseConjunctionExp steps') xs with
             | SomeE x ->
               let (e, rest) = x in
               (match expect (')'::[]) rest with
                | SomeE x0 -> let (_, rest') = x0 in SomeE (e, rest')
                | NoneE err -> NoneE err)
             | NoneE _ ->
               (match parseProductExp steps' xs with
                | SomeE x ->
                  let (e, rest) = x in
                  (match firstExpect ('='::[]) (parseAExp steps') rest with
                   | SomeE x0 ->
                     let (e', rest') = x0 in SomeE ((BEq (e, e')), rest')
                   | NoneE _ ->
                     (match firstExpect ('<'::('='::[])) (parseAExp steps')
                              rest with
                      | SomeE x0 ->
                        let (e', rest') = x0 in SomeE ((BLe (e, e')), rest')
                      | NoneE _ ->
                        NoneE
                          ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('\''::('='::('\''::(' '::('o'::('r'::(' '::('\''::('<'::('='::('\''::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('a'::('r'::('i'::('t'::('h'::('m'::('e'::('t'::('i'::('c'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))))))
                | NoneE err -> NoneE err)))))
    steps

(** val parseConjunctionExp :
    int -> token list -> (bexp * token list) optionE **)

and parseConjunctionExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseAtomicExp steps' xs with
    | SomeE x ->
      let (e, rest) = x in
      (match many (firstExpect ('&'::('&'::[])) (parseAtomicExp steps'))
               steps' rest with
       | SomeE x0 ->
         let (es, rest') = x0 in
         SomeE ((fold_left (fun x1 x2 -> BAnd (x1, x2)) es e), rest')
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseBExp : int -> token list -> (bexp * token list) optionE **)

let parseBExp =
  parseConjunctionExp

(** val parseSimpleCommand :
    int -> token list -> (com * token list) optionE **)

let rec parseSimpleCommand steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match expect ('S'::('K'::('I'::('P'::[])))) xs with
    | SomeE x -> let (_, rest) = x in SomeE (CSkip, rest)
    | NoneE _ ->
      (match firstExpect ('T'::('E'::('S'::('T'::[])))) (parseBExp steps') xs with
       | SomeE x ->
         let (e, rest) = x in
         (match firstExpect ('T'::('H'::('E'::('N'::[]))))
                  (parseSequencedCommand steps') rest with
          | SomeE x0 ->
            let (c, rest') = x0 in
            (match firstExpect ('E'::('L'::('S'::('E'::[]))))
                     (parseSequencedCommand steps') rest' with
             | SomeE x1 ->
               let (c', rest'') = x1 in
               (match expect ('E'::('N'::('D'::[]))) rest'' with
                | SomeE x2 ->
                  let (_, rest''') = x2 in SomeE ((CIf (e, c, c')), rest''')
                | NoneE err -> NoneE err)
             | NoneE err -> NoneE err)
          | NoneE err -> NoneE err)
       | NoneE _ ->
         (match firstExpect ('W'::('H'::('I'::('L'::('E'::[])))))
                  (parseBExp steps') xs with
          | SomeE x ->
            let (e, rest) = x in
            (match firstExpect ('D'::('O'::[]))
                     (parseSequencedCommand steps') rest with
             | SomeE x0 ->
               let (c, rest') = x0 in
               (match expect ('E'::('N'::('D'::[]))) rest' with
                | SomeE x1 ->
                  let (_, rest'') = x1 in SomeE ((CWhile (e, c)), rest'')
                | NoneE err -> NoneE err)
             | NoneE err -> NoneE err)
          | NoneE _ ->
            (match parseIdentifier xs with
             | SomeE x ->
               let (i, rest) = x in
               (match firstExpect (':'::(':'::('='::[]))) (parseAExp steps')
                        rest with
                | SomeE x0 ->
                  let (e, rest') = x0 in SomeE ((CAss (i, e)), rest')
                | NoneE err -> NoneE err)
             | NoneE _ ->
               NoneE
                 ('E'::('x'::('p'::('e'::('c'::('t'::('i'::('n'::('g'::(' '::('a'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::[])))))))))))))))))))))))
    steps

(** val parseSequencedCommand :
    int -> token list -> (com * token list) optionE **)

and parseSequencedCommand steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseSimpleCommand steps' xs with
    | SomeE x ->
      let (c, rest) = x in
      (match firstExpect (';'::(';'::[])) (parseSequencedCommand steps') rest with
       | SomeE x0 -> let (c', rest') = x0 in SomeE ((CSeq (c, c')), rest')
       | NoneE _ -> SomeE (c, rest))
    | NoneE err -> NoneE err)
    steps

(** val bignumber : int **)

let bignumber =
  (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val parse : char list -> com optionE **)

let parse str =
  let tokens = tokenize str in
  (match parseSequencedCommand bignumber tokens with
   | SomeE x ->
     let (c, l) = x in
     (match l with
      | [] -> SomeE c
      | t :: _ ->
        NoneE
          (append
            ('T'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::(' '::('t'::('o'::('k'::('e'::('n'::('s'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('i'::('n'::('g'::(':'::(' '::[])))))))))))))))))))))))))))
            t))
   | NoneE err -> NoneE err)
