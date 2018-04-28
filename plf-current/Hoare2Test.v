Set Warnings "-notation-overridden,-parsing".
Require Import Hoare2.
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

Require Import Hoare2.
Import Check.

Goal True.

idtac "-------------------  if_minus_plus_reloaded  --------------------".
idtac " ".

idtac "#> Manually graded: if_minus_plus_reloaded".
idtac "Possible points: 2".
print_manual_grade score_if_minus_plus_reloaded.
idtac " ".

idtac "-------------------  slow_assignment  --------------------".
idtac " ".

idtac "#> Manually graded: slow_assignment".
idtac "Possible points: 2".
print_manual_grade score_slow_assignment.
idtac " ".

idtac "-------------------  factorial  --------------------".
idtac " ".

idtac "#> Manually graded: factorial".
idtac "Possible points: 3".
print_manual_grade score_factorial.
idtac " ".

idtac "-------------------  Min_Hoare  --------------------".
idtac " ".

idtac "#> Manually graded: Min_Hoare".
idtac "Possible points: 3".
print_manual_grade score_Min_Hoare.
idtac " ".

idtac "-------------------  two_loops  --------------------".
idtac " ".

idtac "#> Manually graded: two_loops".
idtac "Possible points: 3".
print_manual_grade score_two_loops.
idtac " ".

idtac "-------------------  slow_assignment_dec  --------------------".
idtac " ".

idtac "#> Manually graded: slow_assignment_dec".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade score_slow_assignment_dec.
idtac " ".

idtac "#> slow_assignment_dec_correct".
idtac "Advanced".
idtac "Possible points: 2".
check_type @slow_assignment_dec_correct (
(forall m : nat, dec_correct (slow_assignment_dec m))).
idtac "Assumptions:".
Abort.
Print Assumptions slow_assignment_dec_correct.
Goal True.
idtac " ".

idtac "-------------------  factorial_dec  --------------------".
idtac " ".

idtac "#> Manually graded: factorial_dec".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_factorial_dec.
idtac " ".

idtac " ".

idtac "Max points - standard: 13".
idtac "Max points - advanced: 20".
Abort.
