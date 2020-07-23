Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Selection.

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

From VFA Require Import Selection.
Import Check.

Goal True.

idtac "-------------------  select_perm  --------------------".
idtac " ".

idtac "#> select_perm".
idtac "Possible points: 3".
check_type @select_perm (
(forall (x : nat) (l : list nat),
 let (y, r) := select x l in @Permutation.Permutation nat (x :: l) (y :: r))).
idtac "Assumptions:".
Abort.
Print Assumptions select_perm.
Goal True.
idtac " ".

idtac "-------------------  selection_sort_perm  --------------------".
idtac " ".

idtac "#> selection_sort_perm".
idtac "Possible points: 3".
check_type @selection_sort_perm (
(forall l : list nat, @Permutation.Permutation nat l (selection_sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions selection_sort_perm.
Goal True.
idtac " ".

idtac "-------------------  select_smallest  --------------------".
idtac " ".

idtac "#> select_smallest".
idtac "Possible points: 3".
check_type @select_smallest (
(forall (x : nat) (al : list nat) (y : nat) (bl : list nat),
 select x al = (y, bl) -> @Forall nat (fun z : nat => y <= z) bl)).
idtac "Assumptions:".
Abort.
Print Assumptions select_smallest.
Goal True.
idtac " ".

idtac "-------------------  selection_sort_sorted  --------------------".
idtac " ".

idtac "#> selection_sort_sorted".
idtac "Possible points: 3".
check_type @selection_sort_sorted ((forall al : list nat, sorted (selection_sort al))).
idtac "Assumptions:".
Abort.
Print Assumptions selection_sort_sorted.
Goal True.
idtac " ".

idtac "-------------------  selsort'_perm  --------------------".
idtac " ".

idtac "#> selsort'_perm".
idtac "Possible points: 3".
check_type @selsort'_perm (
(forall (n : nat) (l : list nat),
 @length nat l = n -> @Permutation.Permutation nat l (selsort' l))).
idtac "Assumptions:".
Abort.
Print Assumptions selsort'_perm.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
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
idtac "---------- select_perm ---------".
Print Assumptions select_perm.
idtac "---------- selection_sort_perm ---------".
Print Assumptions selection_sort_perm.
idtac "---------- select_smallest ---------".
Print Assumptions select_smallest.
idtac "---------- selection_sort_sorted ---------".
Print Assumptions selection_sort_sorted.
idtac "---------- selsort'_perm ---------".
Print Assumptions selsort'_perm.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-07-23 21:52:52 (UTC+00) *)
