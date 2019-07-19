Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Induction.

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

From LF Require Import Induction.
Import Check.

Goal True.

idtac "-------------------  basic_induction  --------------------".
idtac " ".

idtac "#> mult_0_r".
idtac "Possible points: 0.5".
check_type @mult_0_r ((forall n : nat, n * 0 = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_0_r.
Goal True.
idtac " ".

idtac "#> plus_n_Sm".
idtac "Possible points: 0.5".
check_type @plus_n_Sm ((forall n m : nat, S (n + m) = n + S m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_n_Sm.
Goal True.
idtac " ".

idtac "#> plus_comm".
idtac "Possible points: 0.5".
check_type @plus_comm ((forall n m : nat, n + m = m + n)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_comm.
Goal True.
idtac " ".

idtac "#> plus_assoc".
idtac "Possible points: 0.5".
check_type @plus_assoc ((forall n m p : nat, n + (m + p) = n + m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_assoc.
Goal True.
idtac " ".

idtac "-------------------  double_plus  --------------------".
idtac " ".

idtac "#> double_plus".
idtac "Possible points: 2".
check_type @double_plus ((forall n : nat, double n = n + n)).
idtac "Assumptions:".
Abort.
Print Assumptions double_plus.
Goal True.
idtac " ".

idtac "-------------------  destruct_induction  --------------------".
idtac " ".

idtac "#> Manually graded: destruct_induction".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_destruct_induction.
idtac " ".

idtac "-------------------  plus_comm_informal  --------------------".
idtac " ".

idtac "#> Manually graded: plus_comm_informal".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_plus_comm_informal.
idtac " ".

idtac "-------------------  mult_comm  --------------------".
idtac " ".

idtac "#> mult_comm".
idtac "Possible points: 3".
check_type @mult_comm ((forall m n : nat, m * n = n * m)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_comm.
Goal True.
idtac " ".

idtac "-------------------  binary_commute  --------------------".
idtac " ".

idtac "#> Manually graded: binary_commute".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_binary_commute.
idtac " ".

idtac "-------------------  binary_inverse  --------------------".
idtac " ".

idtac "#> Manually graded: binary_inverse_a".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_binary_inverse_a.
idtac " ".

idtac "#> Manually graded: binary_inverse_b".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_binary_inverse_b.
idtac " ".

idtac "#> Manually graded: binary_inverse_c".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_binary_inverse_c.
idtac " ".

idtac " ".

idtac "Max points - standard: 11".
idtac "Max points - advanced: 18".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- mult_0_r ---------".
Print Assumptions mult_0_r.
idtac "---------- plus_n_Sm ---------".
Print Assumptions plus_n_Sm.
idtac "---------- plus_comm ---------".
Print Assumptions plus_comm.
idtac "---------- plus_assoc ---------".
Print Assumptions plus_assoc.
idtac "---------- double_plus ---------".
Print Assumptions double_plus.
idtac "---------- destruct_induction ---------".
idtac "MANUAL".
idtac "---------- mult_comm ---------".
Print Assumptions mult_comm.
idtac "---------- binary_commute ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- plus_comm_informal ---------".
idtac "MANUAL".
idtac "---------- binary_inverse_a ---------".
idtac "MANUAL".
idtac "---------- binary_inverse_b ---------".
idtac "MANUAL".
idtac "---------- binary_inverse_c ---------".
idtac "MANUAL".
Abort.

(* Fri Jul 19 00:32:23 UTC 2019 *)
