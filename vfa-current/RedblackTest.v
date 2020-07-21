Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Redblack.

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

From VFA Require Import Redblack.
Import Check.

Goal True.

idtac "-------------------  ins_SearchTree  --------------------".
idtac " ".

idtac "#> ins_SearchTree".
idtac "Possible points: 2".
check_type @ins_SearchTree (
(forall (V : Type) (x : Extract.int) (vx : V) (s : tree V)
   (lo hi : BinNums.Z),
 BinInt.Z.le lo (Extract.int2Z x) ->
 BinInt.Z.lt (Extract.int2Z x) hi ->
 SearchTree' V lo s hi -> SearchTree' V lo (ins V x vx s) hi)).
idtac "Assumptions:".
Abort.
Print Assumptions ins_SearchTree.
Goal True.
idtac " ".

idtac "-------------------  valid  --------------------".
idtac " ".

idtac "#> empty_tree_SearchTree".
idtac "Possible points: 1".
check_type @empty_tree_SearchTree ((forall V : Type, SearchTree V (empty_tree V))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_tree_SearchTree.
Goal True.
idtac " ".

idtac "#> insert_SearchTree".
idtac "Possible points: 1".
check_type @insert_SearchTree (
(forall (V : Type) (x : key) (vx : V) (s : tree V),
 SearchTree V s -> SearchTree V (insert V x vx s))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_SearchTree.
Goal True.
idtac " ".

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> lookup_relate".
idtac "Possible points: 3".
check_type @lookup_relate (
(forall (V : Type) (default : V) (k : key) (t : tree V)
   (cts : Extract.IntMaps.total_map V),
 Abs V default t cts -> lookup V default k t = cts (Extract.int2Z k))).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  balance_relate  --------------------".
idtac " ".

idtac "#> balance_relate".
idtac "Possible points: 6".
check_type @balance_relate (
(forall (V : Type) (default : V) (c : color) (l : tree V) 
   (k : key) (vk : V) (r : tree V) (m : Extract.IntMaps.total_map V),
 SearchTree V (T V c l k vk r) ->
 Abs V default (T V c l k vk r) m -> Abs V default (balance V c l k vk r) m)).
idtac "Assumptions:".
Abort.
Print Assumptions balance_relate.
Goal True.
idtac " ".

idtac "-------------------  ins_relate  --------------------".
idtac " ".

idtac "#> ins_relate".
idtac "Possible points: 3".
check_type @ins_relate (
(forall (V : Type) (default : V) (k : key) (v : V) 
   (t : tree V) (cts : Extract.IntMaps.total_map V),
 SearchTree V t ->
 Abs V default t cts ->
 Abs V default (ins V k v t)
   (@Extract.IntMaps.t_update V cts (Extract.int2Z k) v))).
idtac "Assumptions:".
Abort.
Print Assumptions ins_relate.
Goal True.
idtac " ".

idtac "-------------------  is_redblack_properties  --------------------".
idtac " ".

idtac "#> is_redblack_toblack".
idtac "Possible points: 1.5".
check_type @is_redblack_toblack (
(forall (V : Type) (s : tree V) (n : nat),
 is_redblack V s Red n -> is_redblack V s Black n)).
idtac "Assumptions:".
Abort.
Print Assumptions is_redblack_toblack.
Goal True.
idtac " ".

idtac "#> makeblack_fiddle".
idtac "Possible points: 1.5".
check_type @makeblack_fiddle (
(forall (V : Type) (s : tree V) (n : nat),
 is_redblack V s Black n ->
 exists n0 : nat, is_redblack V (makeBlack V s) Red n0)).
idtac "Assumptions:".
Abort.
Print Assumptions makeblack_fiddle.
Goal True.
idtac " ".

idtac "#> ins_is_redblack".
idtac "Possible points: 1.5".
check_type @ins_is_redblack (
(forall (V : Type) (x : key) (vx : V) (s : tree V) (n : nat),
 (is_redblack V s Black n -> nearly_redblack V (ins V x vx s) n) /\
 (is_redblack V s Red n -> is_redblack V (ins V x vx s) Black n))).
idtac "Assumptions:".
Abort.
Print Assumptions ins_is_redblack.
Goal True.
idtac " ".

idtac "#> insert_is_redblack".
idtac "Possible points: 1.5".
check_type @insert_is_redblack (
(forall (V : Type) (x : key) (xv : V) (s : tree V) (n : nat),
 is_redblack V s Red n ->
 exists n' : nat, is_redblack V (insert V x xv s) Red n')).
idtac "Assumptions:".
Abort.
Print Assumptions insert_is_redblack.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 22".
idtac "Max points - advanced: 22".
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
idtac "---------- ins_SearchTree ---------".
Print Assumptions ins_SearchTree.
idtac "---------- empty_tree_SearchTree ---------".
Print Assumptions empty_tree_SearchTree.
idtac "---------- insert_SearchTree ---------".
Print Assumptions insert_SearchTree.
idtac "---------- lookup_relate ---------".
Print Assumptions lookup_relate.
idtac "---------- balance_relate ---------".
Print Assumptions balance_relate.
idtac "---------- ins_relate ---------".
Print Assumptions ins_relate.
idtac "---------- is_redblack_toblack ---------".
Print Assumptions is_redblack_toblack.
idtac "---------- makeblack_fiddle ---------".
Print Assumptions makeblack_fiddle.
idtac "---------- ins_is_redblack ---------".
Print Assumptions ins_is_redblack.
idtac "---------- insert_is_redblack ---------".
Print Assumptions insert_is_redblack.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-07-21 18:41:48 (UTC+00) *)
