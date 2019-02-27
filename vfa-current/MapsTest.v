Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Maps.

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

From VFA Require Import Maps.
Import Check.

Goal True.

idtac "-------------------  eqb_idP  --------------------".
idtac " ".

idtac "#> eqb_idP".
idtac "Possible points: 2".
check_type @eqb_idP ((forall x y : nat, Bool.reflect (x = y) (PeanoNat.Nat.eqb x y))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_idP.
Goal True.
idtac " ".

idtac "-------------------  t_update_same  --------------------".
idtac " ".

idtac "#> t_update_same".
idtac "Possible points: 2".
check_type @t_update_same (
(forall (X : Type) (x : nat) (m : total_map X), @t_update X m x (m x) = m)).
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
(forall (X : Type) (v1 v2 : X) (x1 x2 : nat) (m : total_map X),
 x2 <> x1 ->
 @t_update X (@t_update X m x2 v2) x1 v1 =
 @t_update X (@t_update X m x1 v1) x2 v2)).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_permute.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- eqb_idP ---------".
Print Assumptions eqb_idP.
idtac "---------- t_update_same ---------".
Print Assumptions t_update_same.
idtac "---------- t_update_permute ---------".
Print Assumptions t_update_permute.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Wed Feb 27 15:30:07 UTC 2019 *)
