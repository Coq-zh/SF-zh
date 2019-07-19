Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Sub.

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

From PLF Require Import Sub.
Import Check.

Goal True.

idtac "-------------------  arrow_sub_wrong  --------------------".
idtac " ".

idtac "#> Manually graded: arrow_sub_wrong".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_arrow_sub_wrong.
idtac " ".

idtac "-------------------  subtype_order  --------------------".
idtac " ".

idtac "#> Manually graded: subtype_order".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_subtype_order.
idtac " ".

idtac "-------------------  subtype_instances_tf_2  --------------------".
idtac " ".

idtac "#> Manually graded: subtype_instances_tf_2".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_subtype_instances_tf_2.
idtac " ".

idtac "-------------------  subtype_concepts_tf  --------------------".
idtac " ".

idtac "#> Manually graded: subtype_concepts_tf".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_subtype_concepts_tf.
idtac " ".

idtac "-------------------  proper_subtypes  --------------------".
idtac " ".

idtac "#> Manually graded: proper_subtypes".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_proper_subtypes.
idtac " ".

idtac "-------------------  small_large_1  --------------------".
idtac " ".

idtac "#> Manually graded: small_large_1".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_small_large_1.
idtac " ".

idtac "-------------------  small_large_2  --------------------".
idtac " ".

idtac "#> Manually graded: small_large_2".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_small_large_2.
idtac " ".

idtac "-------------------  small_large_4  --------------------".
idtac " ".

idtac "#> Manually graded: small_large_4".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_small_large_4.
idtac " ".

idtac "-------------------  smallest_1  --------------------".
idtac " ".

idtac "#> Manually graded: smallest_1".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_smallest_1.
idtac " ".

idtac "-------------------  smallest_2  --------------------".
idtac " ".

idtac "#> Manually graded: smallest_2".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_smallest_2.
idtac " ".

idtac "-------------------  pair_permutation  --------------------".
idtac " ".

idtac "#> Manually graded: pair_permutation".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_pair_permutation.
idtac " ".

idtac "-------------------  sub_inversion_arrow  --------------------".
idtac " ".

idtac "#> sub_inversion_arrow".
idtac "Possible points: 3".
check_type @sub_inversion_arrow (
(forall U V1 V2 : ty,
 U <: Arrow V1 V2 ->
 exists U1 U2 : ty, U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2)).
idtac "Assumptions:".
Abort.
Print Assumptions sub_inversion_arrow.
Goal True.
idtac " ".

idtac "-------------------  variations  --------------------".
idtac " ".

idtac "#> Manually graded: variations".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_variations.
idtac " ".

idtac "-------------------  products  --------------------".
idtac " ".

idtac "#> Manually graded: products".
idtac "Possible points: 5".
print_manual_grade manual_grade_for_products.
idtac " ".

idtac " ".

idtac "Max points - standard: 30".
idtac "Max points - advanced: 30".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- arrow_sub_wrong ---------".
idtac "MANUAL".
idtac "---------- subtype_order ---------".
idtac "MANUAL".
idtac "---------- subtype_instances_tf_2 ---------".
idtac "MANUAL".
idtac "---------- subtype_concepts_tf ---------".
idtac "MANUAL".
idtac "---------- proper_subtypes ---------".
idtac "MANUAL".
idtac "---------- small_large_1 ---------".
idtac "MANUAL".
idtac "---------- small_large_2 ---------".
idtac "MANUAL".
idtac "---------- small_large_4 ---------".
idtac "MANUAL".
idtac "---------- smallest_1 ---------".
idtac "MANUAL".
idtac "---------- smallest_2 ---------".
idtac "MANUAL".
idtac "---------- pair_permutation ---------".
idtac "MANUAL".
idtac "---------- sub_inversion_arrow ---------".
Print Assumptions sub_inversion_arrow.
idtac "---------- variations ---------".
idtac "MANUAL".
idtac "---------- products ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:33:50 UTC 2019 *)
