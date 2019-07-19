Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import IndProp.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import IndProp.
Import Check.

Goal True.

idtac "-------------------  ev_double  --------------------".
idtac " ".

idtac "#> ev_double".
idtac "Possible points: 1".
check_type @ev_double ((forall n : nat, even (double n))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_double.
Goal True.
idtac " ".

idtac "-------------------  inversion_practice  --------------------".
idtac " ".

idtac "#> SSSSev__even".
idtac "Possible points: 1".
check_type @SSSSev__even ((forall n : nat, even (S (S (S (S n)))) -> even n)).
idtac "Assumptions:".
Abort.
Print Assumptions SSSSev__even.
Goal True.
idtac " ".

idtac "-------------------  even5_nonsense  --------------------".
idtac " ".

idtac "#> even5_nonsense".
idtac "Possible points: 1".
check_type @even5_nonsense ((even 5 -> 2 + 2 = 9)).
idtac "Assumptions:".
Abort.
Print Assumptions even5_nonsense.
Goal True.
idtac " ".

idtac "-------------------  ev_sum  --------------------".
idtac " ".

idtac "#> ev_sum".
idtac "Possible points: 2".
check_type @ev_sum ((forall n m : nat, even n -> even m -> even (n + m))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_sum.
Goal True.
idtac " ".

idtac "-------------------  ev_ev__ev  --------------------".
idtac " ".

idtac "#> ev_ev__ev".
idtac "Advanced".
idtac "Possible points: 3".
check_type @ev_ev__ev ((forall n m : nat, even (n + m) -> even n -> even m)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_ev__ev.
Goal True.
idtac " ".

idtac "-------------------  R_provability  --------------------".
idtac " ".

idtac "#> Manually graded: R.R_provability".
idtac "Possible points: 3".
print_manual_grade R.manual_grade_for_R_provability.
idtac " ".

idtac "-------------------  subsequence  --------------------".
idtac " ".

idtac "#> subseq_refl".
idtac "Advanced".
idtac "Possible points: 1".
check_type @subseq_refl ((forall l : list nat, subseq l l)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_refl.
Goal True.
idtac " ".

idtac "#> subseq_app".
idtac "Advanced".
idtac "Possible points: 1".
check_type @subseq_app (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l1 (l2 ++ l3))).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_app.
Goal True.
idtac " ".

idtac "-------------------  exp_match_ex1  --------------------".
idtac " ".

idtac "#> empty_is_empty".
idtac "Possible points: 1".
check_type @empty_is_empty ((forall (T : Type) (s : list T), ~ (s =~ @EmptySet T))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_is_empty.
Goal True.
idtac " ".

idtac "#> MUnion'".
idtac "Possible points: 1".
check_type @MUnion' (
(forall (T : Type) (s : list T) (re1 re2 : @reg_exp T),
 s =~ re1 \/ s =~ re2 -> s =~ @Union T re1 re2)).
idtac "Assumptions:".
Abort.
Print Assumptions MUnion'.
Goal True.
idtac " ".

idtac "#> MStar'".
idtac "Possible points: 1".
check_type @MStar' (
(forall (T : Type) (ss : list (list T)) (re : @reg_exp T),
 (forall s : list T, @In (list T) s ss -> s =~ re) ->
 @fold (list T) (list T) (@app T) ss [ ] =~ @Star T re)).
idtac "Assumptions:".
Abort.
Print Assumptions MStar'.
Goal True.
idtac " ".

idtac "-------------------  re_not_empty  --------------------".
idtac " ".

idtac "#> re_not_empty".
idtac "Possible points: 2".
check_type @re_not_empty ((forall T : Type, @reg_exp T -> bool)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty.
Goal True.
idtac " ".

idtac "#> re_not_empty_correct".
idtac "Possible points: 2".
check_type @re_not_empty_correct (
(forall (T : Type) (re : @reg_exp T),
 (exists s : list T, s =~ re) <-> @re_not_empty T re = true)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty_correct.
Goal True.
idtac " ".

idtac "-------------------  pumping  --------------------".
idtac " ".

idtac "#> Pumping.pumping".
idtac "Advanced".
idtac "Possible points: 5".
check_type @Pumping.pumping (
(forall (T : Type) (re : @reg_exp T) (s : list T),
 s =~ re ->
 @Pumping.pumping_constant T re <= @length T s ->
 exists s1 s2 s3 : list T,
   s = s1 ++ s2 ++ s3 /\
   s2 <> [ ] /\ (forall m : nat, s1 ++ @Pumping.napp T m s2 ++ s3 =~ re))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.pumping.
Goal True.
idtac " ".

idtac "-------------------  reflect_iff  --------------------".
idtac " ".

idtac "#> reflect_iff".
idtac "Possible points: 2".
check_type @reflect_iff ((forall (P : Prop) (b : bool), reflect P b -> P <-> b = true)).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_iff.
Goal True.
idtac " ".

idtac "-------------------  eqbP_practice  --------------------".
idtac " ".

idtac "#> eqbP_practice".
idtac "Possible points: 3".
check_type @eqbP_practice (
(forall (n : nat) (l : list nat), count n l = 0 -> ~ @In nat n l)).
idtac "Assumptions:".
Abort.
Print Assumptions eqbP_practice.
Goal True.
idtac " ".

idtac "-------------------  nostutter_defn  --------------------".
idtac " ".

idtac "#> Manually graded: nostutter".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_nostutter.
idtac " ".

idtac "-------------------  filter_challenge  --------------------".
idtac " ".

idtac "#> Manually graded: filter_challenge".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade manual_grade_for_filter_challenge.
idtac " ".

idtac " ".

idtac "Max points - standard: 23".
idtac "Max points - advanced: 37".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- ev_double ---------".
Print Assumptions ev_double.
idtac "---------- SSSSev__even ---------".
Print Assumptions SSSSev__even.
idtac "---------- even5_nonsense ---------".
Print Assumptions even5_nonsense.
idtac "---------- ev_sum ---------".
Print Assumptions ev_sum.
idtac "---------- R_provability ---------".
idtac "MANUAL".
idtac "---------- empty_is_empty ---------".
Print Assumptions empty_is_empty.
idtac "---------- MUnion' ---------".
Print Assumptions MUnion'.
idtac "---------- MStar' ---------".
Print Assumptions MStar'.
idtac "---------- re_not_empty ---------".
Print Assumptions re_not_empty.
idtac "---------- re_not_empty_correct ---------".
Print Assumptions re_not_empty_correct.
idtac "---------- reflect_iff ---------".
Print Assumptions reflect_iff.
idtac "---------- eqbP_practice ---------".
Print Assumptions eqbP_practice.
idtac "---------- nostutter ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- ev_ev__ev ---------".
Print Assumptions ev_ev__ev.
idtac "---------- subseq_refl ---------".
Print Assumptions subseq_refl.
idtac "---------- subseq_app ---------".
Print Assumptions subseq_app.
idtac "---------- Pumping.pumping ---------".
Print Assumptions Pumping.pumping.
idtac "---------- filter_challenge ---------".
idtac "MANUAL".
Abort.

(* Fri Jul 19 00:32:30 UTC 2019 *)
