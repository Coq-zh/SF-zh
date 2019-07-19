Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Smallstep.

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

From PLF Require Import Smallstep.
Import Check.

Goal True.

idtac "-------------------  test_step_2  --------------------".
idtac " ".

idtac "#> SimpleArith1.test_step_2".
idtac "Possible points: 1".
check_type @SimpleArith1.test_step_2 (
(SimpleArith1.step (P (C 0) (P (C 2) (P (C 0) (C 3))))
   (P (C 0) (P (C 2) (C (0 + 3)))))).
idtac "Assumptions:".
Abort.
Print Assumptions SimpleArith1.test_step_2.
Goal True.
idtac " ".

idtac "-------------------  redo_determinism  --------------------".
idtac " ".

idtac "#> step_deterministic".
idtac "Possible points: 3".
check_type @step_deterministic ((@deterministic tm step)).
idtac "Assumptions:".
Abort.
Print Assumptions step_deterministic.
Goal True.
idtac " ".

idtac "-------------------  smallstep_bools  --------------------".
idtac " ".

idtac "#> Manually graded: Temp4.smallstep_bools".
idtac "Possible points: 1".
print_manual_grade Temp4.manual_grade_for_smallstep_bools.
idtac " ".

idtac "-------------------  smallstep_bool_shortcut  --------------------".
idtac " ".

idtac "#> Temp4.Temp5.bool_step_prop4_holds".
idtac "Possible points: 2".
check_type @Temp4.Temp5.bool_step_prop4_holds (Temp4.Temp5.bool_step_prop4).
idtac "Assumptions:".
Abort.
Print Assumptions Temp4.Temp5.bool_step_prop4_holds.
Goal True.
idtac " ".

idtac "-------------------  test_multistep_4  --------------------".
idtac " ".

idtac "#> test_multistep_4".
idtac "Possible points: 2".
check_type @test_multistep_4 (
(P (C 0) (P (C 2) (P (C 0) (C 3))) -->* P (C 0) (C (2 + (0 + 3))))).
idtac "Assumptions:".
Abort.
Print Assumptions test_multistep_4.
Goal True.
idtac " ".

idtac "-------------------  multistep_congr_2  --------------------".
idtac " ".

idtac "#> multistep_congr_2".
idtac "Possible points: 2".
check_type @multistep_congr_2 (
(forall t1 t2 t2' : tm, value t1 -> t2 -->* t2' -> P t1 t2 -->* P t1 t2')).
idtac "Assumptions:".
Abort.
Print Assumptions multistep_congr_2.
Goal True.
idtac " ".

idtac "-------------------  eval__multistep  --------------------".
idtac " ".

idtac "#> eval__multistep".
idtac "Possible points: 3".
check_type @eval__multistep ((forall (t : tm) (n : nat), t ==> n -> t -->* C n)).
idtac "Assumptions:".
Abort.
Print Assumptions eval__multistep.
Goal True.
idtac " ".

idtac "-------------------  eval__multistep_inf  --------------------".
idtac " ".

idtac "#> Manually graded: eval__multistep_inf".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_eval__multistep_inf.
idtac " ".

idtac "-------------------  step__eval  --------------------".
idtac " ".

idtac "#> step__eval".
idtac "Possible points: 3".
check_type @step__eval ((forall (t t' : tm) (n : nat), t --> t' -> t' ==> n -> t ==> n)).
idtac "Assumptions:".
Abort.
Print Assumptions step__eval.
Goal True.
idtac " ".

idtac "-------------------  multistep__eval  --------------------".
idtac " ".

idtac "#> multistep__eval".
idtac "Possible points: 3".
check_type @multistep__eval (
(forall t t' : tm, normal_form_of t t' -> exists n : nat, t' = C n /\ t ==> n)).
idtac "Assumptions:".
Abort.
Print Assumptions multistep__eval.
Goal True.
idtac " ".

idtac "-------------------  combined_properties  --------------------".
idtac " ".

idtac "#> Manually graded: combined_properties".
idtac "Possible points: 4".
print_manual_grade manual_grade_for_combined_properties.
idtac " ".

idtac "-------------------  compiler_is_correct  --------------------".
idtac " ".

idtac "#> compiler_is_correct".
idtac "Advanced".
idtac "Possible points: 3".
check_type @compiler_is_correct (compiler_is_correct_statement).
idtac "Assumptions:".
Abort.
Print Assumptions compiler_is_correct.
Goal True.
idtac " ".

idtac "-------------------  normalize_ex  --------------------".
idtac " ".

idtac "#> normalize_ex".
idtac "Possible points: 1".
check_type @normalize_ex ((exists e' : tm, P (C 3) (P (C 2) (C 1)) -->* e' /\ value e')).
idtac "Assumptions:".
Abort.
Print Assumptions normalize_ex.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 25".
idtac "Max points - advanced: 31".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- SimpleArith1.test_step_2 ---------".
Print Assumptions SimpleArith1.test_step_2.
idtac "---------- step_deterministic ---------".
Print Assumptions step_deterministic.
idtac "---------- smallstep_bools ---------".
idtac "MANUAL".
idtac "---------- Temp4.Temp5.bool_step_prop4_holds ---------".
Print Assumptions Temp4.Temp5.bool_step_prop4_holds.
idtac "---------- test_multistep_4 ---------".
Print Assumptions test_multistep_4.
idtac "---------- multistep_congr_2 ---------".
Print Assumptions multistep_congr_2.
idtac "---------- eval__multistep ---------".
Print Assumptions eval__multistep.
idtac "---------- step__eval ---------".
Print Assumptions step__eval.
idtac "---------- multistep__eval ---------".
Print Assumptions multistep__eval.
idtac "---------- combined_properties ---------".
idtac "MANUAL".
idtac "---------- normalize_ex ---------".
Print Assumptions normalize_ex.
idtac "".
idtac "********** Advanced **********".
idtac "---------- eval__multistep_inf ---------".
idtac "MANUAL".
idtac "---------- compiler_is_correct ---------".
Print Assumptions compiler_is_correct.
Abort.

(* Fri Jul 19 00:33:33 UTC 2019 *)
