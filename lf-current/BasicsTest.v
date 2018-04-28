Set Warnings "-notation-overridden,-parsing".
Require Import Basics.
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

Require Import Basics.
Import Check.

Goal True.

idtac "-------------------  nandb  --------------------".
idtac " ".

idtac "#> test_nandb4".
idtac "Possible points: 1".
check_type @test_nandb4 ((nandb true true = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb4.
Goal True.
idtac " ".

idtac "-------------------  andb3  --------------------".
idtac " ".

idtac "#> test_andb34".
idtac "Possible points: 1".
check_type @test_andb34 ((andb3 true true false = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb34.
Goal True.
idtac " ".

idtac "-------------------  factorial  --------------------".
idtac " ".

idtac "#> test_factorial2".
idtac "Possible points: 1".
check_type @test_factorial2 ((factorial 5 = 10 * 12)).
idtac "Assumptions:".
Abort.
Print Assumptions test_factorial2.
Goal True.
idtac " ".

idtac "-------------------  blt_nat  --------------------".
idtac " ".

idtac "#> test_blt_nat3".
idtac "Possible points: 1".
check_type @test_blt_nat3 ((blt_nat 4 2 = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_blt_nat3.
Goal True.
idtac " ".

idtac "-------------------  plus_id_exercise  --------------------".
idtac " ".

idtac "#> plus_id_exercise".
idtac "Possible points: 1".
check_type @plus_id_exercise ((forall n m o : nat, n = m -> m = o -> n + m = m + o)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_id_exercise.
Goal True.
idtac " ".

idtac "-------------------  mult_S_1  --------------------".
idtac " ".

idtac "#> mult_S_1".
idtac "Possible points: 2".
check_type @mult_S_1 ((forall n m : nat, m = S n -> m * (1 + n) = m * m)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_S_1.
Goal True.
idtac " ".

idtac "-------------------  andb_true_elim2  --------------------".
idtac " ".

idtac "#> andb_true_elim2".
idtac "Possible points: 2".
check_type @andb_true_elim2 ((forall b c : bool, b && c = true -> c = true)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_elim2.
Goal True.
idtac " ".

idtac "-------------------  zero_nbeq_plus_1  --------------------".
idtac " ".

idtac "#> zero_nbeq_plus_1".
idtac "Possible points: 1".
check_type @zero_nbeq_plus_1 ((forall n : nat, beq_nat 0 (n + 1) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions zero_nbeq_plus_1.
Goal True.
idtac " ".

idtac "-------------------  boolean_functions  --------------------".
idtac " ".

idtac "#> identity_fn_applied_twice".
idtac "Possible points: 1".
check_type @identity_fn_applied_twice (
(forall f : bool -> bool,
 (forall x : bool, f x = x) -> forall b : bool, f (f b) = b)).
idtac "Assumptions:".
Abort.
Print Assumptions identity_fn_applied_twice.
Goal True.
idtac " ".

idtac "#> Manually graded: boolean_functions".
idtac "Possible points: 1".
print_manual_grade score_boolean_functions.
idtac " ".

idtac "-------------------  binary  --------------------".
idtac " ".

idtac "#> Manually graded: binary".
idtac "Possible points: 3".
print_manual_grade score_binary.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
Abort.
