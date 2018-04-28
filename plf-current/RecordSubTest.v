Set Warnings "-notation-overridden,-parsing".
Require Import RecordSub.
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

Require Import RecordSub.
Import Check.

Goal True.

idtac "-------------------  subtyping_example_1  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_1".
idtac "Possible points: 2".
check_type @Examples.subtyping_example_1 ((Examples.TRcd_kj <: Examples.TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_1.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_2  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_2".
idtac "Possible points: 1".
check_type @Examples.subtyping_example_2 (
(TArrow TTop Examples.TRcd_kj <:
 TArrow (TArrow Examples.C Examples.C) Examples.TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_2.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_3  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_3".
idtac "Possible points: 1".
check_type @Examples.subtyping_example_3 (
(TArrow TRNil (TRCons "j" Examples.A TRNil) <:
 TArrow (TRCons "k" Examples.B TRNil) TRNil)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_3.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_4  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_4".
idtac "Possible points: 2".
check_type @Examples.subtyping_example_4 (
(TRCons "x" Examples.A (TRCons "y" Examples.B (TRCons "z" Examples.C TRNil)) <:
 TRCons "z" Examples.C (TRCons "y" Examples.B (TRCons "x" Examples.A TRNil)))).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_4.
Goal True.
idtac " ".

idtac "-------------------  rcd_types_match_informal  --------------------".
idtac " ".

idtac "#> Manually graded: rcd_types_match_informal".
idtac "Possible points: 3".
print_manual_grade score_rcd_types_match_informal.
idtac " ".

idtac "-------------------  typing_example_0  --------------------".
idtac " ".

idtac "#> Examples2.typing_example_0".
idtac "Possible points: 1".
check_type @Examples2.typing_example_0 (
(@Maps.empty ty
 |- trcons "k" (tabs "z" Examples.A (tvar "z"))
      (trcons "j" (tabs "z" Examples.B (tvar "z")) trnil) \in
 Examples.TRcd_kj)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples2.typing_example_0.
Goal True.
idtac " ".

idtac "-------------------  typing_example_1  --------------------".
idtac " ".

idtac "#> Examples2.typing_example_1".
idtac "Possible points: 2".
check_type @Examples2.typing_example_1 (
(@Maps.empty ty
 |- tapp (tabs "x" Examples.TRcd_j (tproj (tvar "x") "j")) Examples2.trcd_kj \in
 TArrow Examples.B Examples.B)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples2.typing_example_1.
Goal True.
idtac " ".

idtac "-------------------  canonical_forms_of_arrow_types  --------------------".
idtac " ".

idtac "#> canonical_forms_of_arrow_types".
idtac "Possible points: 3".
check_type @canonical_forms_of_arrow_types (
(forall (Gamma : context) (s : tm) (T1 T2 : ty),
 Gamma |- s \in TArrow T1 T2 ->
 value s -> exists (x : String.string) (S1 : ty) (s2 : tm), s = tabs x S1 s2)).
idtac "Assumptions:".
Abort.
Print Assumptions canonical_forms_of_arrow_types.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
Abort.
