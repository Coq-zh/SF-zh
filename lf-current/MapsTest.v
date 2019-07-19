Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Maps.

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

From LF Require Import Maps.
Import Check.

Goal True.

idtac "-------------------  t_update_same  --------------------".
idtac " ".

idtac "#> t_update_same".
idtac "Possible points: 2".
check_type @t_update_same (
(forall (A : Type) (m : total_map A) (x : string), (x !-> m x; m) = m)).
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
(forall (A : Type) (m : total_map A) (v1 v2 : A) (x1 x2 : string),
 x2 <> x1 -> (x1 !-> v1; x2 !-> v2; m) = (x2 !-> v2; x1 !-> v1; m))).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_permute.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- t_update_same ---------".
Print Assumptions t_update_same.
idtac "---------- t_update_permute ---------".
Print Assumptions t_update_permute.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:32:30 UTC 2019 *)
