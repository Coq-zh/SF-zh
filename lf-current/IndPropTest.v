Set Warnings "-notation-overridden,-parsing".
Require Import IndProp.
Parameter MISSING: Type.   

Module Check.  

Ltac check_type A B :=  
match type of A with  
| context[MISSING] => idtac "Missing:" A  
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]  
end.  

Ltac print_manual_grade A :=  
first [  
match eval compute in A with  
| ?T => idtac "Score:" T  
end  
| idtac "Score: Ungraded"].  

End Check.

Require Import IndProp.
Import Check.

Goal True.

idtac "-------------------  ev_double  --------------------".
idtac " ".

idtac "#> ev_double".
idtac "Possible points: 1".
check_type @ev_double ((forall n : nat, ev (double n))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_double.
Goal True.
idtac " ".

idtac "-------------------  SSSSev__even  --------------------".
idtac " ".

idtac "#> SSSSev__even".
idtac "Possible points: 1".
check_type @SSSSev__even ((forall n : nat, ev (S (S (S (S n)))) -> ev n)).
idtac "Assumptions:".
Abort.
Print Assumptions SSSSev__even.
Goal True.
idtac " ".

idtac "-------------------  even5_nonsense  --------------------".
idtac " ".

idtac "#> even5_nonsense".
idtac "Possible points: 1".
check_type @even5_nonsense ((ev 5 -> 2 + 2 = 9)).
idtac "Assumptions:".
Abort.
Print Assumptions even5_nonsense.
Goal True.
idtac " ".

idtac "-------------------  ev_sum  --------------------".
idtac " ".

idtac "#> ev_sum".
idtac "Possible points: 2".
check_type @ev_sum ((forall n m : nat, ev n -> ev m -> ev (n + m))).
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
check_type @ev_ev__ev ((forall n m : nat, ev (n + m) -> ev n -> ev m)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_ev__ev.
Goal True.
idtac " ".

idtac "-------------------  R_provability  --------------------".
idtac " ".

idtac "#> Manually graded: R_provability".
idtac "Possible points: 3".
print_manual_grade score_R_provability.
idtac " ".

idtac "-------------------  subsequence  --------------------".
idtac " ".

idtac "#> Manually graded: subsequence".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_subsequence.
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

idtac "-------------------  beq_natP_practice  --------------------".
idtac " ".

idtac "#> beq_natP_practice".
idtac "Possible points: 3".
check_type @beq_natP_practice (
(forall (n : nat) (l : list nat), count n l = 0 -> ~ @In nat n l)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_natP_practice.
Goal True.
idtac " ".

idtac "-------------------  nostutter_defn  --------------------".
idtac " ".

idtac "#> Manually graded: nostutter_defn".
idtac "Possible points: 3".
print_manual_grade score_nostutter_defn.
idtac " ".

idtac "-------------------  filter_challenge  --------------------".
idtac " ".

idtac "#> Manually graded: filter_challenge".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_filter_challenge.
idtac " ".

idtac " ".

idtac "Max points - standard: 23".
idtac "Max points - advanced: 39".
Abort.
