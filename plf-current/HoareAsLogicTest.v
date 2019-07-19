Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import HoareAsLogic.

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

From PLF Require Import HoareAsLogic.
Import Check.

Goal True.

idtac "-------------------  hoare_proof_sound  --------------------".
idtac " ".

idtac "#> hoare_proof_sound".
idtac "Possible points: 2".
check_type @hoare_proof_sound (
(forall (P : Hoare.Assertion) (c : Imp.com) (Q : Hoare.Assertion),
 hoare_proof P c Q -> Hoare.hoare_triple P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_proof_sound.
Goal True.
idtac " ".

idtac "-------------------  wp_is_precondition  --------------------".
idtac " ".

idtac "#> wp_is_precondition".
idtac "Possible points: 1".
check_type @wp_is_precondition (
(forall (c : Imp.com) (Q : Hoare.Assertion), Hoare.hoare_triple (wp c Q) c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions wp_is_precondition.
Goal True.
idtac " ".

idtac "-------------------  wp_is_weakest  --------------------".
idtac " ".

idtac "#> wp_is_weakest".
idtac "Possible points: 1".
check_type @wp_is_weakest (
(forall (c : Imp.com) (Q P' : Hoare.Assertion),
 Hoare.hoare_triple P' c Q -> forall st : Imp.state, P' st -> wp c Q st)).
idtac "Assumptions:".
Abort.
Print Assumptions wp_is_weakest.
Goal True.
idtac " ".

idtac "-------------------  hoare_proof_complete  --------------------".
idtac " ".

idtac "#> hoare_proof_complete".
idtac "Possible points: 5".
check_type @hoare_proof_complete (
(forall (P : Hoare.Assertion) (c : Imp.com) (Q : Hoare.Assertion),
 Hoare.hoare_triple P c Q -> hoare_proof P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_proof_complete.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 9".
idtac "Max points - advanced: 9".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- hoare_proof_sound ---------".
Print Assumptions hoare_proof_sound.
idtac "---------- wp_is_precondition ---------".
Print Assumptions wp_is_precondition.
idtac "---------- wp_is_weakest ---------".
Print Assumptions wp_is_weakest.
idtac "---------- hoare_proof_complete ---------".
Print Assumptions hoare_proof_complete.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:33:30 UTC 2019 *)
