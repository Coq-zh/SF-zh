Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare.

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

From PLF Require Import Hoare.
Import Check.

Goal True.

idtac "-------------------  hoare_asgn_examples  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_examples".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_hoare_asgn_examples.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_wrong".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_hoare_asgn_wrong.
idtac " ".

idtac "-------------------  hoare_asgn_fwd  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd".
idtac "Advanced".
idtac "Possible points: 3".
check_type @hoare_asgn_fwd (
(forall (m : nat) (a : Imp.aexp) (P : Imp.state -> Prop),
 {{fun st : Imp.state => P st /\ st Imp.X = m}} Imp.CAss Imp.X a
 {{fun st : Imp.state =>
   P (@Maps.t_update nat st Imp.X m) /\
   st Imp.X = Imp.aeval (@Maps.t_update nat st Imp.X m) a}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_examples_2  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_examples_2".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_hoare_asgn_examples_2.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
({{assert_of_Prop True}}
 Imp.CSeq (Imp.CAss Imp.X (Imp.ANum 1)) (Imp.CAss Imp.Y (Imp.ANum 2))
 {{(fun st0 : Imp.state =>
    (Aexp_of_aexp (Imp.AId Imp.X) st0 = Aexp_of_nat 1 st0)%type) /\
   (fun st0 : Imp.state =>
    (Aexp_of_aexp (Imp.AId Imp.Y) st0 = Aexp_of_nat 2 st0)%type)}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "-------------------  swap_exercise  --------------------".
idtac " ".

idtac "#> swap_exercise".
idtac "Possible points: 3".
check_type @swap_exercise (
({{fun st : Imp.state =>
   Aexp_of_aexp (Imp.AId Imp.X) st <= Aexp_of_aexp (Imp.AId Imp.Y) st}}
 swap_program
 {{fun st : Imp.state =>
   Aexp_of_aexp (Imp.AId Imp.Y) st <= Aexp_of_aexp (Imp.AId Imp.X) st}})).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "-------------------  hoarestate1  --------------------".
idtac " ".

idtac "#> Manually graded: hoarestate1".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_hoarestate1.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
({{assert_of_Prop True}}
 Imp.CIf (Imp.BLe (Imp.AId Imp.X) (Imp.AId Imp.Y))
   (Imp.CAss Imp.Z (Imp.AMinus (Imp.AId Imp.Y) (Imp.AId Imp.X)))
   (Imp.CAss Imp.Y (Imp.APlus (Imp.AId Imp.X) (Imp.AId Imp.Z)))
 {{fun st : Imp.state =>
   Aexp_of_aexp (Imp.AId Imp.Y) st =
   (mkAexp
      (fun st0 : Imp.state =>
       (Aexp_of_aexp (Imp.AId Imp.X) st0 + Aexp_of_aexp (Imp.AId Imp.Z) st0)%nat))
     st}})).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_hoare  --------------------".
idtac " ".

idtac "#> Manually graded: if1_hoare".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_if1_hoare.
idtac " ".

idtac "-------------------  hoare_repeat  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_repeat".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_hoare_repeat.
idtac " ".

idtac "-------------------  hoare_havoc  --------------------".
idtac " ".

idtac "#> Himp.hoare_havoc".
idtac "Possible points: 2".
check_type @Himp.hoare_havoc (
(forall (Q : Assertion) (X : String.string),
 Himp.hoare_triple (Himp.havoc_pre X Q) (Himp.CHavoc X) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".

idtac "#> Himp.havoc_post".
idtac "Possible points: 1".
check_type @Himp.havoc_post (
(forall (P : Assertion) (X : String.string),
 Himp.hoare_triple P (Himp.CHavoc X)
   (fun st : Imp.state => exists n : nat, (P [X |-> Imp.ANum n]) st))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_post.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 25".
idtac "Max points - advanced: 34".
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
idtac "---------- hoare_asgn_examples ---------".
idtac "MANUAL".
idtac "---------- hoare_asgn_wrong ---------".
idtac "MANUAL".
idtac "---------- hoare_asgn_examples_2 ---------".
idtac "MANUAL".
idtac "---------- hoare_asgn_example4 ---------".
Print Assumptions hoare_asgn_example4.
idtac "---------- swap_exercise ---------".
Print Assumptions swap_exercise.
idtac "---------- hoarestate1 ---------".
idtac "MANUAL".
idtac "---------- if_minus_plus ---------".
Print Assumptions if_minus_plus.
idtac "---------- if1_hoare ---------".
idtac "MANUAL".
idtac "---------- Himp.hoare_havoc ---------".
Print Assumptions Himp.hoare_havoc.
idtac "---------- Himp.havoc_post ---------".
Print Assumptions Himp.havoc_post.
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_asgn_fwd ---------".
Print Assumptions hoare_asgn_fwd.
idtac "---------- hoare_repeat ---------".
idtac "MANUAL".
Abort.

(* 2020-08-21 10:33:50 (UTC+00) *)
