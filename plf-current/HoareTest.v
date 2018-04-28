Set Warnings "-notation-overridden,-parsing".
Require Import Hoare.
Parameter MISSING: Type.   

Module Check.  

Ltac check_type A B :=  
match type of A with  
| context[MISSING] => idtac "Missing:" A  
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]  
end.  

Ltac print_manual_grade A :=  
first [  
match eval compute in A with  
| ?T => idtac "Score:" T  
end  
| idtac "Score: Ungraded"].  

End Check.

Require Import Hoare.
Import Check.

Goal True.

idtac "-------------------  hoare_asgn_examples  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_examples".
idtac "Possible points: 2".
print_manual_grade score_hoare_asgn_examples.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_wrong".
idtac "Possible points: 2".
print_manual_grade score_hoare_asgn_wrong.
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
print_manual_grade score_hoare_asgn_examples_2.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
({{fun _ : Imp.state => True}}
 Imp.CSeq (Imp.CAss Imp.X (Imp.ANum 1)) (Imp.CAss Imp.Y (Imp.ANum 2))
 {{fun st : Imp.state => st Imp.X = 1 /\ st Imp.Y = 2}})).
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
({{fun st : Imp.state => st Imp.X <= st Imp.Y}} swap_program
 {{fun st : Imp.state => st Imp.Y <= st Imp.X}})).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "-------------------  hoarestate1  --------------------".
idtac " ".

idtac "#> Manually graded: hoarestate1".
idtac "Possible points: 3".
print_manual_grade score_hoarestate1.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
({{fun _ : Imp.state => True}}
 Imp.CIf (Imp.BLe (Imp.AId Imp.X) (Imp.AId Imp.Y))
   (Imp.CAss Imp.Z (Imp.AMinus (Imp.AId Imp.Y) (Imp.AId Imp.X)))
   (Imp.CAss Imp.Y (Imp.APlus (Imp.AId Imp.X) (Imp.AId Imp.Z)))
 {{fun st : Imp.state => st Imp.Y = st Imp.X + st Imp.Z}})).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_hoare  --------------------".
idtac " ".

idtac "#> Manually graded: if1_hoare".
idtac "Possible points: 4".
print_manual_grade score_if1_hoare.
idtac " ".

idtac "-------------------  hoare_repeat  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_repeat".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_hoare_repeat.
idtac " ".

idtac "-------------------  hoare_havoc  --------------------".
idtac " ".

idtac "#> Himp.hoare_havoc".
idtac "Possible points: 3".
check_type @Himp.hoare_havoc (
(forall (Q : Assertion) (X : String.string),
 Himp.hoare_triple (Himp.havoc_pre X Q) (Himp.CHavoc X) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 23".
idtac "Max points - advanced: 30".
Abort.
