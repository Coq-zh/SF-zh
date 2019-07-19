(** * ImpParser: 用 Coq 实现词法分析和语法分析 *)

(** 在 [Imp.v] 中，我们在设计 Imp 语言时完全忽略了具体的语法问题 ——
    我们仍需将程序员写下的 ASCII 字符串翻译成一棵由 [aexp]、[bexp] 和
    [com] 所定义成的抽象语法树。在本章中，我们将会说明如何用 Coq
    的函数式编程特性来构造简单的词法分析器和语法分析器以填补这一空白。 *)

(** 你无需对本章中代码的所有细节了如指掌，文中对代码的解释十分简短，
    而且本章不包含任何练习：这一章的目的只是为了证明这是办得到的。
    你可以阅读这些代码，它们并不是特别复杂，只是语法分析器的代码使用了一些
    “单子式（Monadic）”的编程习语，可能会稍微有些难以理解；
    但是大部分的读者大概只会粗略看一眼，然后跳到末尾的“例子”一节。 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
Import ListNotations.
From LF Require Import Maps Imp.

(* ################################################################# *)
(** * 内部结构 *)

(* ================================================================= *)
(** ** 词法分析 *)

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)   (* space *)
           (n =? 9))   (* tab *)
      (orb (n =? 10)   (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12=3  223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 语法分析 *)

(* ----------------------------------------------------------------- *)
(** *** 带错误的可选值 *)

(** 一个附带出错信息的 [option] 类型: *)

Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

(** 加一些语法糖以便于编写嵌套的对 [optionE] 的匹配表达式。 *)

Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p => e2
       | NoneE _ => e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).

(* ----------------------------------------------------------------- *)
(** *** 用于构建语法分析器的通用组合子 *)

Open Scope string_scope.

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(** 一个要求符合 [p] 零到多次的、指定步数的词法分析器： *)

Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(** 该词法分析器要求一个给定的词法标记（token），并用 [p] 对其进行处理： *)

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

(** 一个要求某个特定词法标记的语法分析器： *)

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

(* ----------------------------------------------------------------- *)
(** *** 一个 Imp 的递归下降语法分析器 *)

(** 标识符： *)

Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

(** 数字： *)

Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.

(** 解析算术表达式： *)

Fixpoint parsePrimaryExp (steps:nat)
                         (xs : list token)
                       : optionE (aexp * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      TRY ' (i, rest) <- parseIdentifier xs ;;
          SomeE (AId i, rest)
      OR
      TRY ' (n, rest) <- parseNumber xs ;;
          SomeE (ANum n, rest)
      OR
      ' (e, rest) <- firstExpect "(" (parseSumExp steps') xs ;;
      ' (u, rest') <- expect ")" rest ;;
      SomeE (e,rest')
  end

with parseProductExp (steps:nat)
                     (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parsePrimaryExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps'))
                          steps' rest ;;
    SomeE (fold_left AMult es e, rest')
  end

with parseSumExp (steps:nat) (xs : list token)  :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseProductExp steps' xs ;;
    ' (es, rest') <-
        many (fun xs =>
                TRY ' (e,rest') <-
                    firstExpect "+"
                                (parseProductExp steps') xs ;;
                    SomeE ( (true, e), rest')
                OR
                ' (e, rest') <-
                    firstExpect "-"
                                (parseProductExp steps') xs ;;
                SomeE ( (false, e), rest'))
        steps' rest ;;
      SomeE (fold_left (fun e0 term =>
                          match term with
                          | (true,  e) => APlus e0 e
                          | (false, e) => AMinus e0 e
                          end)
                       es e,
             rest')
  end.

Definition parseAExp := parseSumExp.

(** 解析布尔表达式： *)

Fixpoint parseAtomicExp (steps:nat)
                        (xs : list token)  :=
match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
     TRY ' (u,rest) <- expect "true" xs ;;
         SomeE (BTrue,rest)
     OR
     TRY ' (u,rest) <- expect "false" xs ;;
         SomeE (BFalse,rest)
     OR
     TRY ' (e,rest) <- firstExpect "~"
                                   (parseAtomicExp steps')
                                   xs ;;
         SomeE (BNot e, rest)
     OR
     TRY ' (e,rest) <- firstExpect "("
                                   (parseConjunctionExp steps')
                                   xs ;;
         ' (u,rest') <- expect ")" rest ;;
         SomeE (e, rest')
     OR
     ' (e, rest) <- parseProductExp steps' xs ;;
     TRY ' (e', rest') <- firstExpect "="
                                  (parseAExp steps') rest ;;
         SomeE (BEq e e', rest')
     OR
     TRY ' (e', rest') <- firstExpect "<="
                                      (parseAExp steps') rest ;;
         SomeE (BLe e e', rest')
     OR
     NoneE "Expected '=' or '<=' after arithmetic expression"
end

with parseConjunctionExp (steps:nat)
                         (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseAtomicExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "&&"
               (parseAtomicExp steps'))
            steps' rest ;;
    SomeE (fold_left BAnd es e, rest')
  end.

Definition parseBExp := parseConjunctionExp.

Check parseConjunctionExp.

Definition testParsing {X : Type}
           (p : nat ->
                list token ->
                optionE (X * list token))
           (s : string) :=
  let t := tokenize s in
  p 100 t.

(*
Eval compute in
  testParsing parseProductExp "x.y.(x.x).x".

Eval compute in
  testParsing parseConjunctionExp "~(x=x&&x*x<=(x*x)*x)&&x=x".
*)

(** 解析指令： *)

Fixpoint parseSimpleCommand (steps:nat)
                            (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    TRY ' (u, rest) <- expect "SKIP" xs ;;
        SomeE (SKIP%imp, rest)
    OR
    TRY ' (e,rest) <-
            firstExpect "TEST"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "THEN"
                        (parseSequencedCommand steps') rest ;;
        ' (c',rest'') <-
            firstExpect "ELSE"
                        (parseSequencedCommand steps') rest' ;;
        ' (tt,rest''') <-
            expect "END" rest'' ;;
       SomeE(TEST e THEN c ELSE c' FI%imp, rest''')
    OR
    TRY ' (e,rest) <-
            firstExpect "WHILE"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "DO"
                        (parseSequencedCommand steps') rest ;;
        ' (u,rest'') <-
            expect "END" rest' ;;
        SomeE(WHILE e DO c END%imp, rest'')
    OR
    TRY ' (i, rest) <- parseIdentifier xs ;;
        ' (e, rest') <- firstExpect "::=" (parseAExp steps') rest ;;
        SomeE ((i ::= e)%imp, rest')
    OR
        NoneE "Expecting a command"
end

with parseSequencedCommand (steps:nat)
                           (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (c, rest) <- parseSimpleCommand steps' xs ;;
    TRY ' (c', rest') <-
            firstExpect ";;"
                        (parseSequencedCommand steps') rest ;;
        SomeE ((c ;; c')%imp, rest')
    OR
    SomeE (c, rest)
  end.

Definition bignumber := 1000.

Definition parse (str : string) : optionE com :=
  let tokens := tokenize str in
  match parseSequencedCommand bignumber tokens with
  | SomeE (c, []) => SomeE c
  | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err => NoneE err
  end.

(* ################################################################# *)
(** * 示例 *)

Example eg1 : parse "
  TEST x = y + 1 + 2 - y * 6 + 3 THEN
    x ::= x * 1;;
    y ::= 0
  ELSE
    SKIP
  END  "
=
  SomeE (
      TEST "x" = "y" + 1 + 2 - "y" * 6 + 3 THEN
        "x" ::= "x" * 1;;
        "y" ::= 0
      ELSE
        SKIP
      FI)%imp.
Proof. cbv. reflexivity. Qed.

Example eg2 : parse "
  SKIP;;
  z::=x*y*(x*x);;
  WHILE x=x DO
    TEST (z <= z*z) && ~(x = 2) THEN
      x ::= z;;
      y ::= z
    ELSE
      SKIP
    END;;
    SKIP
  END;;
  x::=z  "
=
  SomeE (
      SKIP;;
      "z" ::= "x" * "y" * ("x" * "x");;
      WHILE "x" = "x" DO
        TEST ("z" <= "z" * "z") && ~("x" = 2) THEN
          "x" ::= "z";;
          "y" ::= "z"
        ELSE
          SKIP
        FI;;
        SKIP
      END;;
      "x" ::= "z")%imp.
Proof. cbv. reflexivity. Qed.

(* Fri Jul 19 00:32:21 UTC 2019 *)
