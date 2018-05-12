Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
Require Import StlcProp.
Parameter MISSING: Type. 

Module Check. 

Ltac check_type A B := 
match type of A with 
| context[MISSING] => idtac "Missing:" A  
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"] 
end. 

Ltac print_manual_grade A := 
match eval compute in A with 
| Some (pair ?S ?C) => 
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

Require Import StlcProp.
Import Check.

Goal True.

idtac "-------------------  progress_from_term_ind  --------------------".
idtac " ".

idtac "#> STLCProp.progress'".
idtac "Advanced".
idtac "Possible points: 3".
check_type @STLCProp.progress' (
(forall (t : Stlc.STLC.tm) (T : Stlc.STLC.ty),
 Stlc.STLC.has_type (@Maps.empty Stlc.STLC.ty) t T ->
 Stlc.STLC.value t \/ (exists t' : Stlc.STLC.tm, Stlc.STLC.step t t'))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.progress'.
Goal True.
idtac " ".

idtac "-------------------  afi  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.afi".
idtac "Possible points: 1".
print_manual_grade STLCProp.manual_grade_for_afi.
idtac " ".

idtac "-------------------  subject_expansion_stlc  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.subject_expansion_stlc".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_subject_expansion_stlc.
idtac " ".

idtac "-------------------  types_unique  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.types_unique".
idtac "Possible points: 3".
print_manual_grade STLCProp.manual_grade_for_types_unique.
idtac " ".

idtac "-------------------  progress_preservation_statement  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.progress_preservation_statement".
idtac "Possible points: 1".
print_manual_grade STLCProp.manual_grade_for_progress_preservation_statement.
idtac " ".

idtac "-------------------  stlc_variation1  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.stlc_variation1".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_stlc_variation1.
idtac " ".

idtac "-------------------  stlc_variation2  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.stlc_variation2".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_stlc_variation2.
idtac " ".

idtac "-------------------  stlc_variation3  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.stlc_variation3".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_stlc_variation3.
idtac " ".

idtac "-------------------  stlc_arith  --------------------".
idtac " ".

idtac "#> Manually graded: STLCArith.stlc_arith".
idtac "Possible points: 4".
print_manual_grade STLCArith.manual_grade_for_stlc_arith.
idtac " ".

idtac " ".

idtac "Max points - standard: 17".
idtac "Max points - advanced: 20".
Abort.
