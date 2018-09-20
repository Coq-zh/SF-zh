
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None

type sumbool =
| Left
| Right

(** val add : int -> int -> int **)

let rec add = ( + )

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub n m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> n)
    (fun k ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

(** val eqb : int -> int -> bool **)

let rec eqb = ( = )

(** val leb : int -> int -> bool **)

let rec leb n m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  if b1 then if b2 then Left else Right else if b2 then Right else Left

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (x, x0, x1, x2, x3, x4, x5, x6) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec x b8 with
   | Left ->
     (match bool_dec x0 b9 with
      | Left ->
        (match bool_dec x1 b10 with
         | Left ->
           (match bool_dec x2 b11 with
            | Left ->
              (match bool_dec x3 b12 with
               | Left ->
                 (match bool_dec x4 b13 with
                  | Left ->
                    (match bool_dec x5 b14 with
                     | Left -> bool_dec x6 b15
                     | Right -> Right)
                  | Right -> Right)
               | Right -> Right)
            | Right -> Right)
         | Right -> Right)
      | Right -> Right)
   | Right -> Right)

type string =
| EmptyString
| String of ascii * string

(** val string_dec : string -> string -> sumbool **)

let rec string_dec s x =
  match s with
  | EmptyString -> (match x with
                    | EmptyString -> Left
                    | String (_, _) -> Right)
  | String (a, s0) ->
    (match x with
     | EmptyString -> Right
     | String (a0, s1) ->
       (match ascii_dec a a0 with
        | Left -> string_dec s0 s1
        | Right -> Right))

(** val eqb_string : string -> string -> bool **)

let eqb_string x y =
  match string_dec x y with
  | Left -> true
  | Right -> false

type 'a total_map = string -> 'a

(** val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1 **)

let t_update m x v x' =
  if eqb_string x x' then v else m x'

type state = int total_map

type aexp =
| ANum of int
| AId of string
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
| ANum n -> n
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
| BAnd (b1, b2) -> if beval st b1 then beval st b2 else false

type com =
| CSkip
| CAss of string * aexp
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
