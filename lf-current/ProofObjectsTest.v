Set Warnings "-notation-overridden,-parsing".
Require Import ProofObjects.
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

Require Import ProofObjects.
Import Check.

Goal True.

idtac "-------------------  eight_is_even  --------------------".
idtac " ".

idtac "#> ev_8".
idtac "Possible points: 1".
check_type @ev_8 ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8.
Goal True.
idtac " ".

idtac "#> ev_8'".
idtac "Possible points: 1".
check_type @ev_8' ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8'.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality  --------------------".
idtac " ".

idtac "#> equality__leibniz_equality".
idtac "Possible points: 2".
check_type @equality__leibniz_equality (
(forall (X : Type) (x y : X), x = y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions equality__leibniz_equality.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
Abort.
