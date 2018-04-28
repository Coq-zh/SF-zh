Set Warnings "-notation-overridden,-parsing".
Require Import Typechecking.
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

Require Import Typechecking.
Import Check.

Goal True.

idtac "-------------------  typechecker_extensions  --------------------".
idtac " ".

idtac "#> Manually graded: typechecker_extensions".
idtac "Possible points: 2".
print_manual_grade score_typechecker_extensions.
idtac " ".

idtac "#> Manually graded: typechecker_extensions".
idtac "Possible points: 3".
print_manual_grade score_typechecker_extensions.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
Abort.
