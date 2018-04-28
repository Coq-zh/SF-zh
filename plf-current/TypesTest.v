Set Warnings "-notation-overridden,-parsing".
Require Import Types.
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

Require Import Types.
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
 |- t \in T -> value t \/ (exists t' : tm, t ==> t'))).
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
print_manual_grade score_finish_progress_informal.
idtac " ".

idtac "-------------------  finish_preservation  --------------------".
idtac " ".

idtac "#> preservation".
idtac "Possible points: 2".
check_type @preservation (
(forall (t t' : tm) (T : ty), |- t \in T -> t ==> t' -> |- t' \in T)).
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
print_manual_grade score_finish_preservation_informal.
idtac " ".

idtac "-------------------  preservation_alternate_proof  --------------------".
idtac " ".

idtac "#> preservation'".
idtac "Possible points: 3".
check_type @preservation' (
(forall (t t' : tm) (T : ty), |- t \in T -> t ==> t' -> |- t' \in T)).
idtac "Assumptions:".
Abort.
Print Assumptions preservation'.
Goal True.
idtac " ".

idtac "-------------------  normalize_ex  --------------------".
idtac " ".

idtac "#> NormalizePlayground.normalize_ex".
idtac "Possible points: 1".
check_type @NormalizePlayground.normalize_ex (
(exists e' : Smallstep.tm,
   @Smallstep.multi Smallstep.tm Smallstep.step
     (Smallstep.P (Smallstep.C 3)
        (Smallstep.P (Smallstep.C 2) (Smallstep.C 1))) e')).
idtac "Assumptions:".
Abort.
Print Assumptions NormalizePlayground.normalize_ex.
Goal True.
idtac " ".

idtac "-------------------  subject_expansion  --------------------".
idtac " ".

idtac "#> Manually graded: subject_expansion".
idtac "Possible points: 2".
print_manual_grade score_subject_expansion.
idtac " ".

idtac "-------------------  variation1  --------------------".
idtac " ".

idtac "#> Manually graded: variation1".
idtac "Possible points: 2".
print_manual_grade score_variation1.
idtac " ".

idtac "-------------------  variation2  --------------------".
idtac " ".

idtac "#> Manually graded: variation2".
idtac "Possible points: 2".
print_manual_grade score_variation2.
idtac " ".

idtac "-------------------  remove_predzero  --------------------".
idtac " ".

idtac "#> Manually graded: remove_predzero".
idtac "Possible points: 1".
print_manual_grade score_remove_predzero.
idtac " ".

idtac "-------------------  prog_pres_bigstep  --------------------".
idtac " ".

idtac "#> Manually graded: prog_pres_bigstep".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_prog_pres_bigstep.
idtac " ".

idtac " ".

idtac "Max points - standard: 21".
idtac "Max points - advanced: 31".
Abort.
