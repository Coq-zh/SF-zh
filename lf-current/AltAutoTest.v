Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import AltAuto.

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

From LF Require Import AltAuto.
Import Check.

Goal True.

idtac "-------------------  re_opt  --------------------".
idtac " ".

idtac "#> Manually graded: re_opt".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_re_opt.
idtac " ".

idtac "-------------------  pumping_redux  --------------------".
idtac " ".

idtac "#> Manually graded: pumping_redux".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_pumping_redux.
idtac " ".

idtac " ".

idtac "Max points - standard: 3".
idtac "Max points - advanced: 6".
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
idtac "---------- re_opt ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- pumping_redux ---------".
idtac "MANUAL".
Abort.

(* 2022-03-14 05:27:25 (UTC+00) *)
