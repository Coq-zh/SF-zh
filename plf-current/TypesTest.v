Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Types.

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

From PLF Require Import Types.
Import Check.

Goal True.

idtac "-------------------  some_term_is_stuck  --------------------".
idtac " ".

idtac "#> some_term_is_stuck".
idtac "Possible points: 2".
check_type @some_term_is_stuck ((exists t : tm, stuck t)).
idtac "Assumptions:".
Abort.
Print Assumptions some_term_is_stuck.
Goal True.
idtac " ".

idtac "-------------------  value_is_nf  --------------------".
idtac " ".

idtac "#> value_is_nf".
idtac "Possible points: 3".
check_type @value_is_nf ((forall t : tm, value t -> step_normal_form t)).
idtac "Assumptions:".
Abort.
Print Assumptions value_is_nf.
Goal True.
idtac " ".

idtac "-------------------  finish_progress  --------------------".
idtac " ".

idtac "#> progress".
idtac "Possible points: 3".
check_type @progress (
(forall (t : tm) (T : ty),
 |- t \in T -> value t \/ (exists t' : tm, t --> t'))).
idtac "Assumptions:".
Abort.
Print Assumptions progress.
Goal True.
idtac " ".

idtac "-------------------  finish_progress_informal  --------------------".
idtac " ".

idtac "#> Manually graded: finish_progress_informal".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_finish_progress_informal.
idtac " ".

idtac "-------------------  finish_preservation  --------------------".
idtac " ".

idtac "#> preservation".
idtac "Possible points: 2".
check_type @preservation (
(forall (t t' : tm) (T : ty), |- t \in T -> t --> t' -> |- t' \in T)).
idtac "Assumptions:".
Abort.
Print Assumptions preservation.
Goal True.
idtac " ".

idtac "-------------------  finish_preservation_informal  --------------------".
idtac " ".

idtac "#> Manually graded: finish_preservation_informal".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_finish_preservation_informal.
idtac " ".

idtac "-------------------  preservation_alternate_proof  --------------------".
idtac " ".

idtac "#> preservation'".
idtac "Possible points: 3".
check_type @preservation' (
(forall (t t' : tm) (T : ty), |- t \in T -> t --> t' -> |- t' \in T)).
idtac "Assumptions:".
Abort.
Print Assumptions preservation'.
Goal True.
idtac " ".

idtac "-------------------  subject_expansion  --------------------".
idtac " ".

idtac "#> Manually graded: subject_expansion".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_subject_expansion.
idtac " ".

idtac "-------------------  variation1  --------------------".
idtac " ".

idtac "#> Manually graded: variation1".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_variation1.
idtac " ".

idtac "-------------------  variation2  --------------------".
idtac " ".

idtac "#> Manually graded: variation2".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_variation2.
idtac " ".

idtac "-------------------  remove_prdzro  --------------------".
idtac " ".

idtac "#> Manually graded: remove_predzro".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_remove_predzro.
idtac " ".

idtac "-------------------  prog_pres_bigstep  --------------------".
idtac " ".

idtac "#> Manually graded: prog_pres_bigstep".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade manual_grade_for_prog_pres_bigstep.
idtac " ".

idtac " ".

idtac "Max points - standard: 20".
idtac "Max points - advanced: 30".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- some_term_is_stuck ---------".
Print Assumptions some_term_is_stuck.
idtac "---------- value_is_nf ---------".
Print Assumptions value_is_nf.
idtac "---------- progress ---------".
Print Assumptions progress.
idtac "---------- preservation ---------".
Print Assumptions preservation.
idtac "---------- preservation' ---------".
Print Assumptions preservation'.
idtac "---------- subject_expansion ---------".
idtac "MANUAL".
idtac "---------- variation1 ---------".
idtac "MANUAL".
idtac "---------- variation2 ---------".
idtac "MANUAL".
idtac "---------- remove_predzro ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- finish_progress_informal ---------".
idtac "MANUAL".
idtac "---------- finish_preservation_informal ---------".
idtac "MANUAL".
idtac "---------- prog_pres_bigstep ---------".
idtac "MANUAL".
Abort.

(* Fri Jul 19 00:33:36 UTC 2019 *)
