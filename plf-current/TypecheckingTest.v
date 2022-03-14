Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Typechecking.

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

From PLF Require Import Typechecking.
Import Check.

Goal True.

idtac "-------------------  typechecker_extensions  --------------------".
idtac " ".

idtac "#> Manually graded: TypecheckerExtensions.type_checking_sound".
idtac "Possible points: 4".
print_manual_grade TypecheckerExtensions.manual_grade_for_type_checking_sound.
idtac " ".

idtac "#> Manually graded: TypecheckerExtensions.type_checking_complete".
idtac "Possible points: 6".
print_manual_grade TypecheckerExtensions.manual_grade_for_type_checking_complete.
idtac " ".

idtac " ".

idtac "Max points - standard: 10".
idtac "Max points - advanced: 10".
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
idtac "---------- type_checking_sound ---------".
idtac "MANUAL".
idtac "---------- type_checking_complete ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2022-03-14 05:29:07 (UTC+00) *)
