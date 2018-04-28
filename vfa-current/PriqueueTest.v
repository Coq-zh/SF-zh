Set Warnings "-notation-overridden,-parsing".
Require Import Priqueue.
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

Require Import Priqueue.
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
Abort.
