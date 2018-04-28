Set Warnings "-notation-overridden,-parsing".
Require Import References.
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

Require Import References.
Import Check.

Goal True.

idtac "-------------------  compact_update  --------------------".
idtac " ".

idtac "#> Manually graded: compact_update".
idtac "Possible points: 2".
print_manual_grade score_compact_update.
idtac " ".

idtac "-------------------  type_safety_violation  --------------------".
idtac " ".

idtac "#> Manually graded: type_safety_violation".
idtac "Possible points: 2".
print_manual_grade score_type_safety_violation.
idtac " ".

idtac "-------------------  cyclic_store  --------------------".
idtac " ".

idtac "#> Manually graded: cyclic_store".
idtac "Possible points: 2".
print_manual_grade score_cyclic_store.
idtac " ".

idtac "-------------------  store_not_unique  --------------------".
idtac " ".

idtac "#> Manually graded: store_not_unique".
idtac "Possible points: 2".
print_manual_grade score_store_not_unique.
idtac " ".

idtac "-------------------  preservation_informal  --------------------".
idtac " ".

idtac "#> Manually graded: preservation_informal".
idtac "Possible points: 3".
print_manual_grade score_preservation_informal.
idtac " ".

idtac "-------------------  factorial_ref  --------------------".
idtac " ".

idtac "#> STLCRef.RefsAndNontermination.factorial".
idtac "Possible points: 2".
check_type @STLCRef.RefsAndNontermination.factorial (STLCRef.tm).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial.
Goal True.
idtac " ".

idtac "#> STLCRef.RefsAndNontermination.factorial_type".
idtac "Possible points: 2".
check_type @STLCRef.RefsAndNontermination.factorial_type (
(STLCRef.has_type (@Maps.empty STLCRef.ty) (@nil STLCRef.ty)
   STLCRef.RefsAndNontermination.factorial
   (STLCRef.TArrow STLCRef.TNat STLCRef.TNat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial_type.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
Abort.
