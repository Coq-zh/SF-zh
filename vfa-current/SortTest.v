Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Sort.

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

From VFA Require Import Sort.
Import Check.

Goal True.

idtac "-------------------  insert_perm  --------------------".
idtac " ".

idtac "#> insert_perm".
idtac "Possible points: 3".
check_type @insert_perm (
(forall (x : nat) (l : list nat),
 @Permutation.Permutation nat (x :: l) (insert x l))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_perm.
Goal True.
idtac " ".

idtac "-------------------  sort_perm  --------------------".
idtac " ".

idtac "#> sort_perm".
idtac "Possible points: 3".
check_type @sort_perm ((forall l : list nat, @Permutation.Permutation nat l (sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions sort_perm.
Goal True.
idtac " ".

idtac "-------------------  insert_sorted  --------------------".
idtac " ".

idtac "#> insert_sorted".
idtac "Possible points: 6".
check_type @insert_sorted (
(forall (a : nat) (l : list nat), sorted l -> sorted (insert a l))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_sorted.
Goal True.
idtac " ".

idtac "-------------------  sort_sorted  --------------------".
idtac " ".

idtac "#> sort_sorted".
idtac "Possible points: 2".
check_type @sort_sorted ((forall l : list nat, sorted (sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions sort_sorted.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 14".
idtac "Max points - advanced: 14".
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
idtac "---------- insert_perm ---------".
Print Assumptions insert_perm.
idtac "---------- sort_perm ---------".
Print Assumptions sort_perm.
idtac "---------- insert_sorted ---------".
Print Assumptions insert_sorted.
idtac "---------- sort_sorted ---------".
Print Assumptions sort_sorted.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020年1月16日 *)
