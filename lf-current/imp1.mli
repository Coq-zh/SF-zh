
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : nat -> nat -> bool

val leb : nat -> nat -> bool

val bool_dec : bool -> bool -> sumbool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> sumbool

type string =
| EmptyString
| String of ascii * string

val string_dec : string -> string -> sumbool

val eqb_string : string -> string -> bool

type 'a total_map = string -> 'a

val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1

type state = nat total_map

type aexp =
| ANum of nat
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

val aeval : state -> aexp -> nat

val beval : state -> bexp -> bool

type com =
| CSkip
| CAss of string * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

val ceval_step : state -> com -> nat -> state option
