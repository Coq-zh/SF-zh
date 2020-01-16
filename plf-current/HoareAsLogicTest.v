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

idtac "-------------------  wp_invariant  --------------------".
idtac " ".

idtac "#> wp_invariant".
idtac "Possible points: 2".
check_type @wp_invariant (
(forall (b : Imp.bexp) (c : Imp.com) (Inv Q : Hoare.Assertion),
 Inv = wp (Imp.CWhile b c) Q ->
 Hoare.hoare_triple (fun st : Imp.state => Inv st /\ Hoare.bassn b st) c Inv)).
idtac "Assumptions:".
Abort.
Print Assumptions wp_invariant.
Goal True.
idtac " ".

idtac "-------------------  hoare_proof_complete  --------------------".
idtac " ".

idtac "#> hoare_proof_complete".
idtac "Possible points: 6".
check_type @hoare_proof_complete (
(forall (P : Hoare.Assertion) (c : Imp.com) (Q : Hoare.Assertion),
 Hoare.hoare_triple P c Q -> hoare_proof P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_proof_complete.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 12".
idtac "Max points - advanced: 12".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
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
idtac "---------- hoare_proof_sound ---------".
Print Assumptions hoare_proof_sound.
idtac "---------- wp_is_precondition ---------".
Print Assumptions wp_is_precondition.
idtac "---------- wp_is_weakest ---------".
Print Assumptions wp_is_weakest.
idtac "---------- wp_invariant ---------".
Print Assumptions wp_invariant.
idtac "---------- hoare_proof_complete ---------".
Print Assumptions hoare_proof_complete.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020年1月16日 *)
