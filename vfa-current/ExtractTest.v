Set Warnings "-notation-overridden,-parsing".
Require Import Extract.
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

Require Import Extract.
Import Check.

Goal True.

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> SearchTree2.lookup_relate".
idtac "Possible points: 3".
check_type @SearchTree2.lookup_relate (
(forall (V : Type) (default : V) (k : SearchTree2.key)
   (t : SearchTree2.tree V) (cts : IntMaps.total_map V),
 SearchTree2.Abs V default t cts ->
 SearchTree2.lookup V default k t = cts (int2Z k))).
idtac "Assumptions:".
Abort.
Print Assumptions SearchTree2.lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  insert_relate  --------------------".
idtac " ".

idtac "#> SearchTree2.insert_relate".
idtac "Possible points: 3".
check_type @SearchTree2.insert_relate (
(forall (V : Type) (default : V) (k : SearchTree2.key) 
   (v : V) (t : SearchTree2.tree V) (cts : IntMaps.total_map V),
 SearchTree2.Abs V default t cts ->
 SearchTree2.Abs V default (SearchTree2.insert V k v t)
   (@IntMaps.t_update V cts (int2Z k) v))).
idtac "Assumptions:".
Abort.
Print Assumptions SearchTree2.insert_relate.
Goal True.
idtac " ".

idtac "-------------------  unrealistically_strong_can_relate  --------------------".
idtac " ".

idtac "#> SearchTree2.unrealistically_strong_can_relate".
idtac "Possible points: 1".
check_type @SearchTree2.unrealistically_strong_can_relate (
(forall (V : Type) (default : V) (t : SearchTree2.tree V),
 exists cts : IntMaps.total_map V, SearchTree2.Abs V default t cts)).
idtac "Assumptions:".
Abort.
Print Assumptions SearchTree2.unrealistically_strong_can_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
Abort.
