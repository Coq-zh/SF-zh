Set Warnings "-notation-overridden,-parsing".
Require Import Equiv.
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

Require Import Equiv.
Import Check.

Goal True.

idtac "-------------------  skip_right  --------------------".
idtac " ".

idtac "#> skip_right".
idtac "Possible points: 2".
check_type @skip_right ((forall c : Imp.com, cequiv (Imp.CSeq c Imp.CSkip) c)).
idtac "Assumptions:".
Abort.
Print Assumptions skip_right.
Goal True.
idtac " ".

idtac "-------------------  IFB_false  --------------------".
idtac " ".

idtac "#> IFB_false".
idtac "Possible points: 2".
check_type @IFB_false (
(forall (b : Imp.bexp) (c1 c2 : Imp.com),
 bequiv b Imp.BFalse -> cequiv (Imp.CIf b c1 c2) c2)).
idtac "Assumptions:".
Abort.
Print Assumptions IFB_false.
Goal True.
idtac " ".

idtac "-------------------  swap_if_branches  --------------------".
idtac " ".

idtac "#> swap_if_branches".
idtac "Possible points: 3".
check_type @swap_if_branches (
(forall (b : Imp.bexp) (e1 e2 : Imp.com),
 cequiv (Imp.CIf b e1 e2) (Imp.CIf (Imp.BNot b) e2 e1))).
idtac "Assumptions:".
Abort.
Print Assumptions swap_if_branches.
Goal True.
idtac " ".

idtac "-------------------  WHILE_true  --------------------".
idtac " ".

idtac "#> WHILE_true".
idtac "Possible points: 2".
check_type @WHILE_true (
(forall (b : Imp.bexp) (c : Imp.com),
 bequiv b (Imp.bool_to_bexp true) ->
 cequiv (Imp.CWhile b c) (Imp.CWhile (Imp.bool_to_bexp true) Imp.CSkip))).
idtac "Assumptions:".
Abort.
Print Assumptions WHILE_true.
Goal True.
idtac " ".

idtac "-------------------  assign_aequiv  --------------------".
idtac " ".

idtac "#> assign_aequiv".
idtac "Possible points: 2".
check_type @assign_aequiv (
(forall (X : String.string) (e : Imp.aexp),
 aequiv (Imp.AId X) e -> cequiv Imp.CSkip (Imp.CAss X e))).
idtac "Assumptions:".
Abort.
Print Assumptions assign_aequiv.
Goal True.
idtac " ".

idtac "-------------------  equiv_classes  --------------------".
idtac " ".

idtac "#> Manually graded: equiv_classes".
idtac "Possible points: 2".
print_manual_grade score_equiv_classes.
idtac " ".

idtac "-------------------  CIf_congruence  --------------------".
idtac " ".

idtac "#> CIf_congruence".
idtac "Possible points: 3".
check_type @CIf_congruence (
(forall (b b' : Imp.bexp) (c1 c1' c2 c2' : Imp.com),
 bequiv b b' ->
 cequiv c1 c1' ->
 cequiv c2 c2' -> cequiv (Imp.CIf b c1 c2) (Imp.CIf b' c1' c2'))).
idtac "Assumptions:".
Abort.
Print Assumptions CIf_congruence.
Goal True.
idtac " ".

idtac "-------------------  fold_constants_com_sound  --------------------".
idtac " ".

idtac "#> fold_constants_com_sound".
idtac "Possible points: 3".
check_type @fold_constants_com_sound ((ctrans_sound fold_constants_com)).
idtac "Assumptions:".
Abort.
Print Assumptions fold_constants_com_sound.
Goal True.
idtac " ".

idtac "-------------------  inequiv_exercise  --------------------".
idtac " ".

idtac "#> inequiv_exercise".
idtac "Possible points: 3".
check_type @inequiv_exercise (
(~ cequiv (Imp.CWhile (Imp.bool_to_bexp true) Imp.CSkip) Imp.CSkip)).
idtac "Assumptions:".
Abort.
Print Assumptions inequiv_exercise.
Goal True.
idtac " ".

idtac "-------------------  himp_ceval  --------------------".
idtac " ".

idtac "#> Manually graded: himp_ceval".
idtac "Possible points: 2".
print_manual_grade score_himp_ceval.
idtac " ".

idtac "-------------------  havoc_swap  --------------------".
idtac " ".

idtac "#> Himp.pXY_cequiv_pYX".
idtac "Possible points: 3".
check_type @Himp.pXY_cequiv_pYX (
(Himp.cequiv Himp.pXY Himp.pYX \/ ~ Himp.cequiv Himp.pXY Himp.pYX)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.pXY_cequiv_pYX.
Goal True.
idtac " ".

idtac "-------------------  p1_p2_term  --------------------".
idtac " ".

idtac "#> Himp.p1_may_diverge".
idtac "Advanced".
idtac "Possible points: 2".
check_type @Himp.p1_may_diverge (
(forall (st : String.string -> nat) (st' : Imp.state),
 st Imp.X <> 0 -> ~ Himp.ceval Himp.p1 st st')).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p1_may_diverge.
Goal True.
idtac " ".

idtac "#> Himp.p2_may_diverge".
idtac "Advanced".
idtac "Possible points: 2".
check_type @Himp.p2_may_diverge (
(forall (st : String.string -> nat) (st' : Imp.state),
 st Imp.X <> 0 -> ~ Himp.ceval Himp.p2 st st')).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p2_may_diverge.
Goal True.
idtac " ".

idtac "-------------------  p1_p2_equiv  --------------------".
idtac " ".

idtac "#> Himp.p1_p2_equiv".
idtac "Advanced".
idtac "Possible points: 4".
check_type @Himp.p1_p2_equiv ((Himp.cequiv Himp.p1 Himp.p2)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p1_p2_equiv.
Goal True.
idtac " ".

idtac "-------------------  p3_p4_inequiv  --------------------".
idtac " ".

idtac "#> Himp.p3_p4_inequiv".
idtac "Advanced".
idtac "Possible points: 4".
check_type @Himp.p3_p4_inequiv ((~ Himp.cequiv Himp.p3 Himp.p4)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p3_p4_inequiv.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 27".
idtac "Max points - advanced: 39".
Abort.
