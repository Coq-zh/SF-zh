Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Norm.

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

From PLF Require Import Norm.
Import Check.

Goal True.

idtac "-------------------  norm_fail  --------------------".
idtac " ".

idtac "#> Manually graded: norm_fail".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_norm_fail.
idtac " ".

idtac "-------------------  norm  --------------------".
idtac " ".

idtac "#> Manually graded: norm".
idtac "Possible points: 10".
print_manual_grade manual_grade_for_norm.
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
idtac "---------- norm_fail ---------".
idtac "MANUAL".
idtac "---------- norm ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-05-20 01:29:23 (UTC+00) *)
