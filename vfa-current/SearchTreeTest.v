Set Warnings "-notation-overridden,-parsing".
Require Import SearchTree.
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

Require Import SearchTree.
Import Check.

Goal True.

idtac "-------------------  example_map  --------------------".
idtac " ".

idtac "#> example_map".
idtac "Possible points: 2".
check_type @example_map ((forall V : Type, V -> V -> V -> V -> Maps.total_map V)).
idtac "Assumptions:".
Abort.
Print Assumptions example_map.
Goal True.
idtac " ".

idtac "-------------------  check_example_map  --------------------".
idtac " ".

idtac "#> check_example_map".
idtac "Possible points: 3".
check_type @check_example_map (
(forall (V : Type) (default v2 v4 v5 : V),
 Abs V default (example_tree V v2 v4 v5) (example_map V default v2 v4 v5))).
idtac "Assumptions:".
Abort.
Print Assumptions check_example_map.
Goal True.
idtac " ".

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> lookup_relate".
idtac "Possible points: 3".
check_type @lookup_relate (
(forall (V : Type) (default : V) (k : key) (t : tree V)
   (cts : Maps.total_map V),
 Abs V default t cts -> lookup V default k t = cts k)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  insert_relate  --------------------".
idtac " ".

idtac "#> insert_relate".
idtac "Possible points: 4".
check_type @insert_relate (
(forall (V : Type) (default : V) (k : key) (v : V) 
   (t : tree V) (cts : Maps.total_map V),
 Abs V default t cts ->
 Abs V default (insert V k v t) (@Maps.t_update V cts k v))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_relate.
Goal True.
idtac " ".

idtac "-------------------  elements_relate_informal  --------------------".
idtac " ".

idtac "#> Manually graded: elements_relate_informal".
idtac "Possible points: 3".
print_manual_grade score_elements_relate_informal.
idtac " ".

idtac "-------------------  not_elements_relate  --------------------".
idtac " ".

idtac "#> not_elements_relate".
idtac "Possible points: 4".
check_type @not_elements_relate (
(forall (V : Type) (default v : V),
 v <> default ->
 ~
 (forall (t : tree V) (cts : Maps.total_map V),
  Abs V default t cts -> list2map V default (elements V t) = cts))).
idtac "Assumptions:".
Abort.
Print Assumptions not_elements_relate.
Goal True.
idtac " ".

idtac "-------------------  empty_tree_SearchTree  --------------------".
idtac " ".

idtac "#> empty_tree_SearchTree".
idtac "Possible points: 1".
check_type @empty_tree_SearchTree ((forall V : Type, SearchTree V (empty_tree V))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_tree_SearchTree.
Goal True.
idtac " ".

idtac "-------------------  insert_SearchTree  --------------------".
idtac " ".

idtac "#> insert_SearchTree".
idtac "Possible points: 3".
check_type @insert_SearchTree (
(forall (V : Type) (k : key) (v : V) (t : tree V),
 SearchTree V t -> SearchTree V (insert V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_SearchTree.
Goal True.
idtac " ".

idtac "-------------------  can_relate  --------------------".
idtac " ".

idtac "#> can_relate".
idtac "Possible points: 2".
check_type @can_relate (
(forall (V : Type) (default : V) (t : tree V),
 SearchTree V t -> exists cts : Maps.total_map V, Abs V default t cts)).
idtac "Assumptions:".
Abort.
Print Assumptions can_relate.
Goal True.
idtac " ".

idtac "-------------------  unrealistically_strong_can_relate  --------------------".
idtac " ".

idtac "#> unrealistically_strong_can_relate".
idtac "Possible points: 2".
check_type @unrealistically_strong_can_relate (
(forall (V : Type) (default : V) (t : tree V),
 exists cts : Maps.total_map V, Abs V default t cts)).
idtac "Assumptions:".
Abort.
Print Assumptions unrealistically_strong_can_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 27".
idtac "Max points - advanced: 27".
Abort.
