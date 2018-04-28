Set Warnings "-notation-overridden,-parsing".
Require Import Sort.
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

Require Import Sort.
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
idtac "Possible points: 4".
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

idtac "Max points - standard: 12".
idtac "Max points - advanced: 12".
Abort.
