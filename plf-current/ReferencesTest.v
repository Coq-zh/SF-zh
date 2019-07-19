Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import References.

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

From PLF Require Import References.
Import Check.

Goal True.

idtac "-------------------  compact_update  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.compact_update".
idtac "Possible points: 2".
print_manual_grade STLCRef.manual_grade_for_compact_update.
idtac " ".

idtac "-------------------  type_safety_violation  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.type_safety_violation".
idtac "Possible points: 2".
print_manual_grade STLCRef.manual_grade_for_type_safety_violation.
idtac " ".

idtac "-------------------  cyclic_store  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.cyclic_store".
idtac "Possible points: 2".
print_manual_grade STLCRef.manual_grade_for_cyclic_store.
idtac " ".

idtac "-------------------  store_not_unique  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.store_not_unique".
idtac "Possible points: 2".
print_manual_grade STLCRef.manual_grade_for_store_not_unique.
idtac " ".

idtac "-------------------  preservation_informal  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.preservation_informal".
idtac "Possible points: 3".
print_manual_grade STLCRef.manual_grade_for_preservation_informal.
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
   (STLCRef.Arrow STLCRef.Nat STLCRef.Nat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial_type.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- compact_update ---------".
idtac "MANUAL".
idtac "---------- type_safety_violation ---------".
idtac "MANUAL".
idtac "---------- cyclic_store ---------".
idtac "MANUAL".
idtac "---------- store_not_unique ---------".
idtac "MANUAL".
idtac "---------- preservation_informal ---------".
idtac "MANUAL".
idtac "---------- STLCRef.RefsAndNontermination.factorial ---------".
Print Assumptions STLCRef.RefsAndNontermination.factorial.
idtac "---------- STLCRef.RefsAndNontermination.factorial_type ---------".
Print Assumptions STLCRef.RefsAndNontermination.factorial_type.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:33:59 UTC 2019 *)
