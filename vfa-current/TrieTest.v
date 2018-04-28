Set Warnings "-notation-overridden,-parsing".
Require Import Trie.
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

Require Import Trie.
Import Check.

Goal True.

idtac "-------------------  succ_correct  --------------------".
idtac " ".

idtac "#> Integers.succ_correct".
idtac "Possible points: 2".
check_type @Integers.succ_correct (
(forall p : Integers.positive,
 Integers.positive2nat (Integers.succ p) = S (Integers.positive2nat p))).
idtac "Assumptions:".
Abort.
Print Assumptions Integers.succ_correct.
Goal True.
idtac " ".

idtac "-------------------  addc_correct  --------------------".
idtac " ".

idtac "#> Integers.addc_correct".
idtac "Possible points: 3".
check_type @Integers.addc_correct (
(forall (c : bool) (p q : Integers.positive),
 Integers.positive2nat (Integers.addc c p q) =
 (if c then 1 else 0) + Integers.positive2nat p + Integers.positive2nat q)).
idtac "Assumptions:".
Abort.
Print Assumptions Integers.addc_correct.
Goal True.
idtac " ".

idtac "-------------------  compare_correct  --------------------".
idtac " ".

idtac "#> Integers.compare_correct".
idtac "Possible points: 5".
check_type @Integers.compare_correct (
(forall x y : Integers.positive,
 match Integers.compare x y with
 | Integers.Eq => Integers.positive2nat x = Integers.positive2nat y
 | Integers.Lt => Integers.positive2nat x < Integers.positive2nat y
 | Integers.Gt => Integers.positive2nat x > Integers.positive2nat y
 end)).
idtac "Assumptions:".
Abort.
Print Assumptions Integers.compare_correct.
Goal True.
idtac " ".

idtac "-------------------  successor_of_Z_constant_time  --------------------".
idtac " ".

idtac "#> Manually graded: successor_of_Z_constant_time".
idtac "Possible points: 2".
print_manual_grade score_successor_of_Z_constant_time.
idtac " ".

idtac "-------------------  look_leaf  --------------------".
idtac " ".

idtac "#> look_leaf".
idtac "Possible points: 1".
check_type @look_leaf (
(forall (A : Type) (a : A) (j : BinNums.positive), @look A a j (@Leaf A) = a)).
idtac "Assumptions:".
Abort.
Print Assumptions look_leaf.
Goal True.
idtac " ".

idtac "-------------------  look_ins_same  --------------------".
idtac " ".

idtac "#> look_ins_same".
idtac "Possible points: 2".
check_type @look_ins_same (
(forall (A : Type) (a : A) (k : BinNums.positive) (v : A) (t : trie A),
 @look A a k (@ins A a k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions look_ins_same.
Goal True.
idtac " ".

idtac "-------------------  look_ins_same  --------------------".
idtac " ".

idtac "#> look_ins_same".
idtac "Possible points: 3".
check_type @look_ins_same (
(forall (A : Type) (a : A) (k : BinNums.positive) (v : A) (t : trie A),
 @look A a k (@ins A a k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions look_ins_same.
Goal True.
idtac " ".

idtac "-------------------  pos2nat_bijective  --------------------".
idtac " ".

idtac "#> pos2nat_injective".
idtac "Possible points: 1".
check_type @pos2nat_injective (
(forall p q : BinNums.positive, pos2nat p = pos2nat q -> p = q)).
idtac "Assumptions:".
Abort.
Print Assumptions pos2nat_injective.
Goal True.
idtac " ".

idtac "#> nat2pos_injective".
idtac "Possible points: 1".
check_type @nat2pos_injective ((forall i j : nat, nat2pos i = nat2pos j -> i = j)).
idtac "Assumptions:".
Abort.
Print Assumptions nat2pos_injective.
Goal True.
idtac " ".

idtac "-------------------  is_trie  --------------------".
idtac " ".

idtac "#> is_trie".
idtac "Possible points: 2".
check_type @is_trie ((forall A : Type, trie_table A -> Prop)).
idtac "Assumptions:".
Abort.
Print Assumptions is_trie.
Goal True.
idtac " ".

idtac "-------------------  empty_relate  --------------------".
idtac " ".

idtac "#> empty_relate".
idtac "Possible points: 2".
check_type @empty_relate (
(forall (A : Type) (default : A),
 @Abs A (@empty A default) (@Maps.t_empty A default))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_relate.
Goal True.
idtac " ".

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> lookup_relate".
idtac "Possible points: 2".
check_type @lookup_relate (
(forall (A : Type) (i : BinNums.positive) (t : trie_table A)
   (m : Maps.total_map A),
 @is_trie A t -> @Abs A t m -> @lookup A i t = m (pos2nat i))).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  insert_relate  --------------------".
idtac " ".

idtac "#> insert_relate".
idtac "Possible points: 3".
check_type @insert_relate (
(forall (A : Type) (k : BinNums.positive) (v : A) 
   (t : trie_table A) (cts : Maps.total_map A),
 @is_trie A t ->
 @Abs A t cts ->
 @Abs A (@insert A k v t) (@Maps.t_update A cts (pos2nat k) v))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 29".
idtac "Max points - advanced: 29".
Abort.
