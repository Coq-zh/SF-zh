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
idtac "Possible points: 2".
print_manual_grade TypecheckerExtensions.manual_grade_for_type_checking_sound.
idtac " ".

idtac "#> Manually graded: TypecheckerExtensions.type_checking_complete".
idtac "Possible points: 3".
print_manual_grade TypecheckerExtensions.manual_grade_for_type_checking_complete.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- type_checking_sound ---------".
idtac "MANUAL".
idtac "---------- type_checking_complete ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:33:54 UTC 2019 *)
