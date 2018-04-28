Set Warnings "-notation-overridden,-parsing".
Require Import Bib.
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

Require Import Bib.
Import Check.

Goal True.

idtac " ".

idtac "Max points - standard: 0".
idtac "Max points - advanced: 0".
Abort.
