Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Tactics.

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

From LF Require Import Tactics.
Import Check.

Goal True.

idtac "-------------------  apply_exercise1  --------------------".
idtac " ".

idtac "#> rev_exercise1".
idtac "Possible points: 3".
check_type @rev_exercise1 ((forall l l' : list nat, l = @rev nat l' -> l' = @rev nat l)).
idtac "Assumptions:".
Abort.
Print Assumptions rev_exercise1.
Goal True.
idtac " ".

idtac "-------------------  injection_ex3  --------------------".
idtac " ".

idtac "#> injection_ex3".
idtac "Possible points: 1".
check_type @injection_ex3 (
(forall (X : Type) (x y z : X) (l j : list X),
 x :: y :: l = z :: j -> y :: l = x :: j -> x = y)).
idtac "Assumptions:".
Abort.
Print Assumptions injection_ex3.
Goal True.
idtac " ".

idtac "-------------------  discriminate_ex3  --------------------".
idtac " ".

idtac "#> discriminate_ex3".
idtac "Possible points: 1".
check_type @discriminate_ex3 (
(forall (X : Type) (x y z : X) (l : list X),
 list X -> x :: y :: l = [ ] -> x = z)).
idtac "Assumptions:".
Abort.
Print Assumptions discriminate_ex3.
Goal True.
idtac " ".

idtac "-------------------  plus_n_n_injective  --------------------".
idtac " ".

idtac "#> plus_n_n_injective".
idtac "Possible points: 3".
check_type @plus_n_n_injective ((forall n m : nat, n + n = m + m -> n = m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_n_n_injective.
Goal True.
idtac " ".

idtac "-------------------  eqb_true  --------------------".
idtac " ".

idtac "#> eqb_true".
idtac "Possible points: 2".
check_type @eqb_true ((forall n m : nat, (n =? m) = true -> n = m)).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_true.
Goal True.
idtac " ".

idtac "-------------------  eqb_true_informal  --------------------".
idtac " ".

idtac "#> Manually graded: informal_proof".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_informal_proof.
idtac " ".

idtac "-------------------  gen_dep_practice  --------------------".
idtac " ".

idtac "#> nth_error_after_last".
idtac "Possible points: 3".
check_type @nth_error_after_last (
(forall (n : nat) (X : Type) (l : list X),
 @length X l = n -> @nth_error X l n = @None X)).
idtac "Assumptions:".
Abort.
Print Assumptions nth_error_after_last.
Goal True.
idtac " ".

idtac "-------------------  destruct_eqn_practice  --------------------".
idtac " ".

idtac "#> bool_fn_applied_thrice".
idtac "Possible points: 2".
check_type @bool_fn_applied_thrice (
(forall (f : bool -> bool) (b : bool), f (f (f b)) = f b)).
idtac "Assumptions:".
Abort.
Print Assumptions bool_fn_applied_thrice.
Goal True.
idtac " ".

idtac "-------------------  eqb_sym  --------------------".
idtac " ".

idtac "#> eqb_sym".
idtac "Possible points: 3".
check_type @eqb_sym ((forall n m : nat, (n =? m) = (m =? n))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_sym.
Goal True.
idtac " ".

idtac "-------------------  split_combine  --------------------".
idtac " ".

idtac "#> Manually graded: split_combine".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_split_combine.
idtac " ".

idtac "-------------------  filter_exercise  --------------------".
idtac " ".

idtac "#> filter_exercise".
idtac "Advanced".
idtac "Possible points: 3".
check_type @filter_exercise (
(forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
 @filter X test l = x :: lf -> test x = true)).
idtac "Assumptions:".
Abort.
Print Assumptions filter_exercise.
Goal True.
idtac " ".

idtac "-------------------  forall_exists_challenge  --------------------".
idtac " ".

idtac "#> existsb_existsb'".
idtac "Advanced".
idtac "Possible points: 4".
check_type @existsb_existsb' (
(forall (X : Type) (test : X -> bool) (l : list X),
 @existsb X test l = @existsb' X test l)).
idtac "Assumptions:".
Abort.
Print Assumptions existsb_existsb'.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 18".
idtac "Max points - advanced: 30".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- rev_exercise1 ---------".
Print Assumptions rev_exercise1.
idtac "---------- injection_ex3 ---------".
Print Assumptions injection_ex3.
idtac "---------- discriminate_ex3 ---------".
Print Assumptions discriminate_ex3.
idtac "---------- plus_n_n_injective ---------".
Print Assumptions plus_n_n_injective.
idtac "---------- eqb_true ---------".
Print Assumptions eqb_true.
idtac "---------- nth_error_after_last ---------".
Print Assumptions nth_error_after_last.
idtac "---------- bool_fn_applied_thrice ---------".
Print Assumptions bool_fn_applied_thrice.
idtac "---------- eqb_sym ---------".
Print Assumptions eqb_sym.
idtac "".
idtac "********** Advanced **********".
idtac "---------- informal_proof ---------".
idtac "MANUAL".
idtac "---------- split_combine ---------".
idtac "MANUAL".
idtac "---------- filter_exercise ---------".
Print Assumptions filter_exercise.
idtac "---------- existsb_existsb' ---------".
Print Assumptions existsb_existsb'.
Abort.

(* Fri Jul 19 00:32:26 UTC 2019 *)
