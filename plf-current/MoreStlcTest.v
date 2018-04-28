Set Warnings "-notation-overridden,-parsing".
Require Import MoreStlc.
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

Require Import MoreStlc.
Import Check.

Goal True.

idtac "-------------------  STLC_extensions  --------------------".
idtac " ".

idtac "#> Manually graded: STLC_extensions".
idtac "Possible points: 5".
print_manual_grade score_STLC_extensions.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
Abort.
