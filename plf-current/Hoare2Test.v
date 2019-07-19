Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare2.

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

From PLF Require Import Hoare2.
Import Check.

Goal True.

idtac "-------------------  if_minus_plus_reloaded  --------------------".
idtac " ".

idtac "#> Manually graded: decorations_in_if_minus_plus_reloaded".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_decorations_in_if_minus_plus_reloaded.
idtac " ".

idtac "-------------------  slow_assignment  --------------------".
idtac " ".

idtac "#> Manually graded: decorations_in_slow_assignment".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_decorations_in_slow_assignment.
idtac " ".

idtac "-------------------  factorial  --------------------".
idtac " ".

idtac "#> Manually graded: decorations_in_factorial".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_decorations_in_factorial.
idtac " ".

idtac "-------------------  Min_Hoare  --------------------".
idtac " ".

idtac "#> Manually graded: decorations_in_Min_Hoare".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_decorations_in_Min_Hoare.
idtac " ".

idtac "-------------------  two_loops  --------------------".
idtac " ".

idtac "#> Manually graded: decorations_in_two_loops".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_decorations_in_two_loops.
idtac " ".

idtac "-------------------  slow_assignment_dec  --------------------".
idtac " ".

idtac "#> Manually graded: check_defn_of_slow_assignment_dec".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_check_defn_of_slow_assignment_dec.
idtac " ".

idtac "#> slow_assignment_dec_correct".
idtac "Advanced".
idtac "Possible points: 2".
check_type @slow_assignment_dec_correct (
(forall m : nat, dec_correct (slow_assignment_dec m))).
idtac "Assumptions:".
Abort.
Print Assumptions slow_assignment_dec_correct.
Goal True.
idtac " ".

idtac "-------------------  factorial_dec  --------------------".
idtac " ".

idtac "#> Manually graded: factorial_dec".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade manual_grade_for_factorial_dec.
idtac " ".

idtac " ".

idtac "Max points - standard: 13".
idtac "Max points - advanced: 20".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- decorations_in_if_minus_plus_reloaded ---------".
idtac "MANUAL".
idtac "---------- decorations_in_slow_assignment ---------".
idtac "MANUAL".
idtac "---------- decorations_in_factorial ---------".
idtac "MANUAL".
idtac "---------- decorations_in_Min_Hoare ---------".
idtac "MANUAL".
idtac "---------- decorations_in_two_loops ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- check_defn_of_slow_assignment_dec ---------".
idtac "MANUAL".
idtac "---------- slow_assignment_dec_correct ---------".
Print Assumptions slow_assignment_dec_correct.
idtac "---------- factorial_dec ---------".
idtac "MANUAL".
Abort.

(* Fri Jul 19 00:33:29 UTC 2019 *)
