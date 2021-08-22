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
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "int2Z".
idtac "ltb_lt".
idtac "ltb".
idtac "Extract.int".
idtac "Extract.int2Z".
idtac "Extract.ltb_lt".
idtac "Extract.ltb".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- TreeTable.gso ---------".
Print Assumptions TreeTable.gso.
idtac "---------- TreeTable2.gso ---------".
Print Assumptions TreeTable2.gso.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2021-08-22 05:57:20 (UTC+00) *)
