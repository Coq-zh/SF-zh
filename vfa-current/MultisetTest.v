Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Multiset.

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

From VFA Require Import Multiset.
Import Check.

Goal True.

idtac "-------------------  union_assoc  --------------------".
idtac " ".

idtac "#> union_assoc".
idtac "Possible points: 1".
check_type @union_assoc (
(forall a b c : multiset, union a (union b c) = union (union a b) c)).
idtac "Assumptions:".
Abort.
Print Assumptions union_assoc.
Goal True.
idtac " ".

idtac "-------------------  union_comm  --------------------".
idtac " ".

idtac "#> union_comm".
idtac "Possible points: 1".
check_type @union_comm ((forall a b : multiset, union a b = union b a)).
idtac "Assumptions:".
Abort.
Print Assumptions union_comm.
Goal True.
idtac " ".

idtac "-------------------  insert_contents  --------------------".
idtac " ".

idtac "#> insert_contents".
idtac "Possible points: 3".
check_type @insert_contents (
(forall (x : value) (l : list value),
 contents (x :: l) = contents (Sort.insert x l))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_contents.
Goal True.
idtac " ".

idtac "-------------------  sort_contents  --------------------".
idtac " ".

idtac "#> sort_contents".
idtac "Possible points: 3".
check_type @sort_contents ((forall l : list value, contents l = contents (Sort.sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions sort_contents.
Goal True.
idtac " ".

idtac "-------------------  permutations_vs_multiset  --------------------".
idtac " ".

idtac "#> Manually graded: permutations_vs_multiset".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_permutations_vs_multiset.
idtac " ".

idtac "-------------------  perm_contents  --------------------".
idtac " ".

idtac "#> perm_contents".
idtac "Possible points: 3".
check_type @perm_contents (
(forall al bl : list nat,
 @Permutation.Permutation nat al bl -> contents al = contents bl)).
idtac "Assumptions:".
Abort.
Print Assumptions perm_contents.
Goal True.
idtac " ".

idtac "-------------------  delete_contents  --------------------".
idtac " ".

idtac "#> delete_contents".
idtac "Possible points: 3".
check_type @delete_contents (
(forall (v : value) (al : list value),
 contents (list_delete al v) = multiset_delete (contents al) v)).
idtac "Assumptions:".
Abort.
Print Assumptions delete_contents.
Goal True.
idtac " ".

idtac "-------------------  contents_perm_aux  --------------------".
idtac " ".

idtac "#> contents_perm_aux".
idtac "Possible points: 2".
check_type @contents_perm_aux (
(forall (v : value) (b : multiset), empty = union (singleton v) b -> False)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_perm_aux.
Goal True.
idtac " ".

idtac "-------------------  contents_in  --------------------".
idtac " ".

idtac "#> contents_in".
idtac "Possible points: 2".
check_type @contents_in (
(forall (a : value) (bl : list value),
 contents bl a > 0 -> @List.In value a bl)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_in.
Goal True.
idtac " ".

idtac "-------------------  in_perm_delete  --------------------".
idtac " ".

idtac "#> in_perm_delete".
idtac "Possible points: 2".
check_type @in_perm_delete (
(forall (a : value) (bl : list value),
 @List.In value a bl ->
 @Permutation.Permutation value (a :: list_delete bl a) bl)).
idtac "Assumptions:".
Abort.
Print Assumptions in_perm_delete.
Goal True.
idtac " ".

idtac "-------------------  contents_perm  --------------------".
idtac " ".

idtac "#> contents_perm".
idtac "Possible points: 6".
check_type @contents_perm (
(forall al bl : list value,
 contents al = contents bl -> @Permutation.Permutation value al bl)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_perm.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 27".
idtac "Max points - advanced: 27".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "int2Z".
idtac "ltb_lt".
idtac "ltb".
idtac "Extract.int".
idtac "Extract.int2Z".
idtac "Extract.ltb_lt".
idtac "Extract.ltb".
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
idtac "---------- union_assoc ---------".
Print Assumptions union_assoc.
idtac "---------- union_comm ---------".
Print Assumptions union_comm.
idtac "---------- insert_contents ---------".
Print Assumptions insert_contents.
idtac "---------- sort_contents ---------".
Print Assumptions sort_contents.
idtac "---------- permutations_vs_multiset ---------".
idtac "MANUAL".
idtac "---------- perm_contents ---------".
Print Assumptions perm_contents.
idtac "---------- delete_contents ---------".
Print Assumptions delete_contents.
idtac "---------- contents_perm_aux ---------".
Print Assumptions contents_perm_aux.
idtac "---------- contents_in ---------".
Print Assumptions contents_in.
idtac "---------- in_perm_delete ---------".
Print Assumptions in_perm_delete.
idtac "---------- contents_perm ---------".
Print Assumptions contents_perm.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-07-21 18:49:18 (UTC+00) *)
