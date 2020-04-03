Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Priqueue.

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

From VFA Require Import Priqueue.
Import Check.

Goal True.

idtac "-------------------  select_perm_and_friends  --------------------".
idtac " ".

idtac "#> List_Priqueue.select_perm".
idtac "Possible points: 1".
check_type @List_Priqueue.select_perm (
(forall (i : nat) (l : list nat),
 let (j, r) := List_Priqueue.select i l in
 @Permutation.Permutation nat (i :: l) (j :: r))).
idtac "Assumptions:".
Abort.
Print Assumptions List_Priqueue.select_perm.
Goal True.
idtac " ".

idtac "#> List_Priqueue.select_biggest_aux".
idtac "Possible points: 1".
check_type @List_Priqueue.select_biggest_aux (
(forall (i : nat) (al : list nat) (j : nat) (bl : list nat),
 @List.Forall nat (fun x : nat => j >= x) bl ->
 List_Priqueue.select i al = (j, bl) -> j >= i)).
idtac "Assumptions:".
Abort.
Print Assumptions List_Priqueue.select_biggest_aux.
Goal True.
idtac " ".

idtac "#> List_Priqueue.select_biggest".
idtac "Possible points: 1".
check_type @List_Priqueue.select_biggest (
(forall (i : nat) (al : list nat) (j : nat) (bl : list nat),
 List_Priqueue.select i al = (j, bl) ->
 @List.Forall nat (fun x : nat => j >= x) bl)).
idtac "Assumptions:".
Abort.
Print Assumptions List_Priqueue.select_biggest.
Goal True.
idtac " ".

idtac "-------------------  simple_priq_proofs  --------------------".
idtac " ".

idtac "#> List_Priqueue.delete_max_None_relate".
idtac "Possible points: 0.5".
check_type @List_Priqueue.delete_max_None_relate (
(forall p : List_Priqueue.priqueue,
 List_Priqueue.priq p ->
 List_Priqueue.Abs p (@nil List_Priqueue.key) <->
 List_Priqueue.delete_max p = @None (nat * list nat))).
idtac "Assumptions:".
Abort.
Print Assumptions List_Priqueue.delete_max_None_relate.
Goal True.
idtac " ".

idtac "#> List_Priqueue.delete_max_Some_relate".
idtac "Possible points: 1".
check_type @List_Priqueue.delete_max_Some_relate (
(forall (p q : List_Priqueue.priqueue) (k : nat)
   (pl ql : list List_Priqueue.key),
 List_Priqueue.priq p ->
 List_Priqueue.Abs p pl ->
 List_Priqueue.delete_max p = @Some (nat * List_Priqueue.priqueue) (k, q) ->
 List_Priqueue.Abs q ql ->
 @Permutation.Permutation List_Priqueue.key pl (k :: ql) /\
 @List.Forall nat (ge k) ql)).
idtac "Assumptions:".
Abort.
Print Assumptions List_Priqueue.delete_max_Some_relate.
Goal True.
idtac " ".

idtac "#> List_Priqueue.delete_max_Some_relate".
idtac "Possible points: 0.5".
check_type @List_Priqueue.delete_max_Some_relate (
(forall (p q : List_Priqueue.priqueue) (k : nat)
   (pl ql : list List_Priqueue.key),
 List_Priqueue.priq p ->
 List_Priqueue.Abs p pl ->
 List_Priqueue.delete_max p = @Some (nat * List_Priqueue.priqueue) (k, q) ->
 List_Priqueue.Abs q ql ->
 @Permutation.Permutation List_Priqueue.key pl (k :: ql) /\
 @List.Forall nat (ge k) ql)).
idtac "Assumptions:".
Abort.
Print Assumptions List_Priqueue.delete_max_Some_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
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
idtac "---------- List_Priqueue.select_perm ---------".
Print Assumptions List_Priqueue.select_perm.
idtac "---------- List_Priqueue.select_biggest_aux ---------".
Print Assumptions List_Priqueue.select_biggest_aux.
idtac "---------- List_Priqueue.select_biggest ---------".
Print Assumptions List_Priqueue.select_biggest.
idtac "---------- List_Priqueue.delete_max_None_relate ---------".
Print Assumptions List_Priqueue.delete_max_None_relate.
idtac "---------- List_Priqueue.delete_max_Some_relate ---------".
Print Assumptions List_Priqueue.delete_max_Some_relate.
idtac "---------- List_Priqueue.delete_max_Some_relate ---------".
Print Assumptions List_Priqueue.delete_max_Some_relate.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-04-03 05:25:45 (UTC+00) *)
