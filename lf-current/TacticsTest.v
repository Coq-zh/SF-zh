Set Warnings "-notation-overridden,-parsing".
Require Import Tactics.
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

Require Import Tactics.
Import Check.

Goal True.

idtac "-------------------  apply_exercise1  --------------------".
idtac " ".

idtac "#> rev_exercise1".
idtac "Possible points: 3".
check_type @rev_exercise1 ((forall l l' : list nat, l = @rev nat l' -> l' = @rev nat l)).
idtac "Assumptions:".
Abort.
Print Assumptions rev_exercise1.
Goal True.
idtac " ".

idtac "-------------------  inversion_ex3  --------------------".
idtac " ".

idtac "#> inversion_ex3".
idtac "Possible points: 1".
check_type @inversion_ex3 (
(forall (X : Type) (x y z : X) (l j : list X),
 x :: y :: l = z :: j -> y :: l = x :: j -> x = y)).
idtac "Assumptions:".
Abort.
Print Assumptions inversion_ex3.
Goal True.
idtac " ".

idtac "-------------------  inversion_ex6  --------------------".
idtac " ".

idtac "#> inversion_ex6".
idtac "Possible points: 1".
check_type @inversion_ex6 (
(forall (X : Type) (x y z : X) (l j : list X),
 x :: y :: l = [ ] -> y :: l = z :: j -> x = z)).
idtac "Assumptions:".
Abort.
Print Assumptions inversion_ex6.
Goal True.
idtac " ".

idtac "-------------------  plus_n_n_injective  --------------------".
idtac " ".

idtac "#> plus_n_n_injective".
idtac "Possible points: 3".
check_type @plus_n_n_injective ((forall n m : nat, n + n = m + m -> n = m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_n_n_injective.
Goal True.
idtac " ".

idtac "-------------------  beq_nat_true  --------------------".
idtac " ".

idtac "#> beq_nat_true".
idtac "Possible points: 2".
check_type @beq_nat_true ((forall n m : nat, beq_nat n m = true -> n = m)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_true.
Goal True.
idtac " ".

idtac "-------------------  beq_nat_true_informal  --------------------".
idtac " ".

idtac "#> Manually graded: beq_nat_true_informal".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade score_beq_nat_true_informal.
idtac " ".

idtac "-------------------  gen_dep_practice  --------------------".
idtac " ".

idtac "#> nth_error_after_last".
idtac "Possible points: 3".
check_type @nth_error_after_last (
(forall (n : nat) (X : Type) (l : list X),
 @length X l = n -> @nth_error X l n = @None X)).
idtac "Assumptions:".
Abort.
Print Assumptions nth_error_after_last.
Goal True.
idtac " ".

idtac "-------------------  destruct_eqn_practice  --------------------".
idtac " ".

idtac "#> bool_fn_applied_thrice".
idtac "Possible points: 2".
check_type @bool_fn_applied_thrice (
(forall (f : bool -> bool) (b : bool), f (f (f b)) = f b)).
idtac "Assumptions:".
Abort.
Print Assumptions bool_fn_applied_thrice.
Goal True.
idtac " ".

idtac "-------------------  beq_nat_sym  --------------------".
idtac " ".

idtac "#> beq_nat_sym".
idtac "Possible points: 3".
check_type @beq_nat_sym ((forall n m : nat, beq_nat n m = beq_nat m n)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_sym.
Goal True.
idtac " ".

idtac "-------------------  split_combine  --------------------".
idtac " ".

idtac "#> Manually graded: split_combine".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade score_split_combine.
idtac " ".

idtac "-------------------  filter_exercise  --------------------".
idtac " ".

idtac "#> filter_exercise".
idtac "Advanced".
idtac "Possible points: 3".
check_type @filter_exercise (
(forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
 @filter X test l = x :: lf -> test x = true)).
idtac "Assumptions:".
Abort.
Print Assumptions filter_exercise.
Goal True.
idtac " ".

idtac "-------------------  forall_exists_challenge  --------------------".
idtac " ".

idtac "#> Manually graded: forall_exists_challenge".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_forall_exists_challenge.
idtac " ".

idtac " ".

idtac "Max points - standard: 18".
idtac "Max points - advanced: 30".
Abort.
