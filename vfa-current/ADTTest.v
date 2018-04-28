Set Warnings "-notation-overridden,-parsing".
Require Import ADT.
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

Require Import ADT.
Import Check.

Goal True.

idtac "-------------------  TreeTable_gso  --------------------".
idtac " ".

idtac "#> TreeTable.gso".
idtac "Possible points: 3".
check_type @TreeTable.gso (
(forall (j k : TreeTable.key) (v : TreeTable.V) (t : TreeTable.table),
 j <> k -> TreeTable.get j (TreeTable.set k v t) = TreeTable.get j t)).
idtac "Assumptions:".
Abort.
Print Assumptions TreeTable.gso.
Goal True.
idtac " ".

idtac "-------------------  TreeTable_gso  --------------------".
idtac " ".

idtac "#> TreeTable2.gso".
idtac "Possible points: 3".
check_type @TreeTable2.gso (
(forall (j k : TreeTable2.key) (v : TreeTable2.V) (t : TreeTable2.table),
 j <> k -> TreeTable2.get j (TreeTable2.set k v t) = TreeTable2.get j t)).
idtac "Assumptions:".
Abort.
Print Assumptions TreeTable2.gso.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 6".
idtac "Max points - advanced: 6".
Abort.
