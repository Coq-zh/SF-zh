Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Basics.

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

From LF Require Import Basics.
Import Check.

Goal True.

idtac "-------------------  nandb  --------------------".
idtac " ".

idtac "#> test_nandb4".
idtac "Possible points: 1".
check_type @test_nandb4 ((nandb true true = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb4.
Goal True.
idtac " ".

idtac "-------------------  andb3  --------------------".
idtac " ".

idtac "#> test_andb34".
idtac "Possible points: 1".
check_type @test_andb34 ((andb3 true true false = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb34.
Goal True.
idtac " ".

idtac "-------------------  factorial  --------------------".
idtac " ".

idtac "#> test_factorial2".
idtac "Possible points: 1".
check_type @test_factorial2 ((factorial 5 = 10 * 12)).
idtac "Assumptions:".
Abort.
Print Assumptions test_factorial2.
Goal True.
idtac " ".

idtac "-------------------  ltb  --------------------".
idtac " ".

idtac "#> test_ltb3".
idtac "Possible points: 1".
check_type @test_ltb3 (((4 <? 2) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_ltb3.
Goal True.
idtac " ".

idtac "-------------------  plus_id_exercise  --------------------".
idtac " ".

idtac "#> plus_id_exercise".
idtac "Possible points: 1".
check_type @plus_id_exercise ((forall n m o : nat, n = m -> m = o -> n + m = m + o)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_id_exercise.
Goal True.
idtac " ".

idtac "-------------------  mult_S_1  --------------------".
idtac " ".

idtac "#> mult_S_1".
idtac "Possible points: 2".
check_type @mult_S_1 ((forall n m : nat, m = S n -> m * (1 + n) = m * m)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_S_1.
Goal True.
idtac " ".

idtac "-------------------  andb_true_elim2  --------------------".
idtac " ".

idtac "#> andb_true_elim2".
idtac "Possible points: 2".
check_type @andb_true_elim2 ((forall b c : bool, b && c = true -> c = true)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_elim2.
Goal True.
idtac " ".

idtac "-------------------  zero_nbeq_plus_1  --------------------".
idtac " ".

idtac "#> zero_nbeq_plus_1".
idtac "Possible points: 1".
check_type @zero_nbeq_plus_1 ((forall n : nat, (0 =? n + 1) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions zero_nbeq_plus_1.
Goal True.
idtac " ".

idtac "-------------------  indentity_fn_applied_twice  --------------------".
idtac " ".

idtac "#> identity_fn_applied_twice".
idtac "Possible points: 1".
check_type @identity_fn_applied_twice (
(forall f : bool -> bool,
 (forall x : bool, f x = x) -> forall b : bool, f (f b) = b)).
idtac "Assumptions:".
Abort.
Print Assumptions identity_fn_applied_twice.
Goal True.
idtac " ".

idtac "-------------------  negation_fn_applied_twice  --------------------".
idtac " ".

idtac "#> Manually graded: negation_fn_applied_twice".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_negation_fn_applied_twice.
idtac " ".

idtac "-------------------  binary  --------------------".
idtac " ".

idtac "#> Manually graded: binary".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_binary.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- test_nandb4 ---------".
Print Assumptions test_nandb4.
idtac "---------- test_andb34 ---------".
Print Assumptions test_andb34.
idtac "---------- test_factorial2 ---------".
Print Assumptions test_factorial2.
idtac "---------- test_ltb3 ---------".
Print Assumptions test_ltb3.
idtac "---------- plus_id_exercise ---------".
Print Assumptions plus_id_exercise.
idtac "---------- mult_S_1 ---------".
Print Assumptions mult_S_1.
idtac "---------- andb_true_elim2 ---------".
Print Assumptions andb_true_elim2.
idtac "---------- zero_nbeq_plus_1 ---------".
Print Assumptions zero_nbeq_plus_1.
idtac "---------- identity_fn_applied_twice ---------".
Print Assumptions identity_fn_applied_twice.
idtac "---------- negation_fn_applied_twice ---------".
idtac "MANUAL".
idtac "---------- binary ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Mar 15 17:06:31 UTC 2019 *)
