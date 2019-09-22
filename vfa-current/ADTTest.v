Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import ADT.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
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

From VFA Require Import ADT.
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
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- TreeTable.gso ---------".
Print Assumptions TreeTable.gso.
idtac "---------- TreeTable2.gso ---------".
Print Assumptions TreeTable2.gso.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Sun Sep 22 20:56:53 UTC 2019 *)
