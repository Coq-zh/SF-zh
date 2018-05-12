Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
Require Import MoreStlc.
Parameter MISSING: Type. 

Module Check. 

Ltac check_type A B := 
match type of A with 
| context[MISSING] => idtac "Missing:" A  
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"] 
end. 

Ltac print_manual_grade A := 
match eval compute in A with 
| Some (pair ?S ?C) => 
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

Require Import MoreStlc.
Import Check.

Goal True.

idtac "-------------------  STLC_extensions  --------------------".
idtac " ".

idtac "#> Manually graded: STLC_extensions".
idtac "Possible points: 5".
print_manual_grade manual_grade_for_STLC_extensions.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
Abort.
