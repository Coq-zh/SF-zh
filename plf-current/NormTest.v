Set Warnings "-notation-overridden,-parsing".
Require Import Norm.
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

Require Import Norm.
Import Check.

Goal True.

idtac "-------------------  norm_fail  --------------------".
idtac " ".

idtac "#> Manually graded: norm_fail".
idtac "Possible points: 2".
print_manual_grade score_norm_fail.
idtac " ".

idtac "-------------------  norm  --------------------".
idtac " ".

idtac "#> Manually graded: norm".
idtac "Possible points: 5".
print_manual_grade score_norm.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
Abort.
