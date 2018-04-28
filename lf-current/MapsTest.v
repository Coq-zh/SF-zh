Set Warnings "-notation-overridden,-parsing".
Require Import Maps.
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

Require Import Maps.
Import Check.

Goal True.

idtac "-------------------  t_update_same  --------------------".
idtac " ".

idtac "#> t_update_same".
idtac "Possible points: 2".
check_type @t_update_same (
(forall (X : Type) (x : string) (m : total_map X), m & {x --> m x} = m)).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_same.
Goal True.
idtac " ".

idtac "-------------------  t_update_permute  --------------------".
idtac " ".

idtac "#> t_update_permute".
idtac "Possible points: 3".
check_type @t_update_permute (
(forall (X : Type) (v1 v2 : X) (x1 x2 : string) (m : total_map X),
 x2 <> x1 -> m & {x2 --> v2; x1 --> v1} = m & {x1 --> v1; x2 --> v2})).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_permute.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
Abort.
