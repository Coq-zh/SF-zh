Set Warnings "-notation-overridden,-parsing".
Require Import Selection.
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

Require Import Selection.
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
 select x al = (y, bl) -> @List.Forall nat (fun z : nat => y <= z) bl)).
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
Abort.
