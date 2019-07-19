Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import ProofObjects.

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

From LF Require Import ProofObjects.
Import Check.

Goal True.

idtac "-------------------  eight_is_even  --------------------".
idtac " ".

idtac "#> ev_8".
idtac "Possible points: 1".
check_type @ev_8 ((even 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8.
Goal True.
idtac " ".

idtac "#> ev_8'".
idtac "Possible points: 1".
check_type @ev_8' ((even 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8'.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality  --------------------".
idtac " ".

idtac "#> MyEquality.equality__leibniz_equality".
idtac "Possible points: 2".
check_type @MyEquality.equality__leibniz_equality (
(forall (X : Type) (x y : X),
 @MyEquality.eq X x y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions MyEquality.equality__leibniz_equality.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- ev_8 ---------".
Print Assumptions ev_8.
idtac "---------- ev_8' ---------".
Print Assumptions ev_8'.
idtac "---------- MyEquality.equality__leibniz_equality ---------".
Print Assumptions MyEquality.equality__leibniz_equality.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:32:31 UTC 2019 *)
