Set Warnings "-notation-overridden,-parsing".
Require Import Decide.
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

Require Import Decide.
Import Check.

Goal True.

idtac "-------------------  insert_sorted_le_dec  --------------------".
idtac " ".

idtac "#> ScratchPad2.insert_sorted".
idtac "Possible points: 2".
check_type @ScratchPad2.insert_sorted (
(forall (a : nat) (l : list nat),
 ScratchPad2.sorted l -> ScratchPad2.sorted (ScratchPad2.insert a l))).
idtac "Assumptions:".
Abort.
Print Assumptions ScratchPad2.insert_sorted.
Goal True.
idtac " ".

idtac "-------------------  list_nat_in  --------------------".
idtac " ".

idtac "#> list_nat_in".
idtac "Possible points: 2".
check_type @list_nat_in (
(forall (i : nat) (al : list nat),
 {@List.In nat i al} + {~ @List.In nat i al})).
idtac "Assumptions:".
Abort.
Print Assumptions list_nat_in.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
Abort.
