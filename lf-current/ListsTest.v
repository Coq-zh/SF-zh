Set Warnings "-notation-overridden,-parsing".
Require Import Lists.
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

Require Import Lists.
Import Check.

Goal True.

idtac "-------------------  snd_fst_is_swap  --------------------".
idtac " ".

idtac "#> NatList.snd_fst_is_swap".
idtac "Possible points: 1".
check_type @NatList.snd_fst_is_swap (
(forall p : NatList.natprod,
 NatList.pair (NatList.snd p) (NatList.fst p) = NatList.swap_pair p)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.snd_fst_is_swap.
Goal True.
idtac " ".

idtac "-------------------  list_funs  --------------------".
idtac " ".

idtac "#> NatList.test_nonzeros".
idtac "Possible points: 0.5".
check_type @NatList.test_nonzeros (
(NatList.nonzeros
   (NatList.cons 0
      (NatList.cons 1
         (NatList.cons 0
            (NatList.cons 2
               (NatList.cons 3 (NatList.cons 0 (NatList.cons 0 NatList.nil))))))) =
 NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_nonzeros.
Goal True.
idtac " ".

idtac "#> NatList.test_oddmembers".
idtac "Possible points: 0.5".
check_type @NatList.test_oddmembers (
(NatList.oddmembers
   (NatList.cons 0
      (NatList.cons 1
         (NatList.cons 0
            (NatList.cons 2
               (NatList.cons 3 (NatList.cons 0 (NatList.cons 0 NatList.nil))))))) =
 NatList.cons 1 (NatList.cons 3 NatList.nil))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_oddmembers.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers2".
idtac "Possible points: 0.5".
check_type @NatList.test_countoddmembers2 (
(NatList.countoddmembers
   (NatList.cons 0 (NatList.cons 2 (NatList.cons 4 NatList.nil))) = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers2.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers3".
idtac "Possible points: 0.5".
check_type @NatList.test_countoddmembers3 ((NatList.countoddmembers NatList.nil = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers3.
Goal True.
idtac " ".

idtac "-------------------  alternate  --------------------".
idtac " ".

idtac "#> NatList.test_alternate1".
idtac "Advanced".
idtac "Possible points: 1".
check_type @NatList.test_alternate1 (
(NatList.alternate
   (NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))
   (NatList.cons 4 (NatList.cons 5 (NatList.cons 6 NatList.nil))) =
 NatList.cons 1
   (NatList.cons 4
      (NatList.cons 2
         (NatList.cons 5 (NatList.cons 3 (NatList.cons 6 NatList.nil))))))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate1.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate2".
idtac "Advanced".
idtac "Possible points: 1".
check_type @NatList.test_alternate2 (
(NatList.alternate (NatList.cons 1 NatList.nil)
   (NatList.cons 4 (NatList.cons 5 (NatList.cons 6 NatList.nil))) =
 NatList.cons 1
   (NatList.cons 4 (NatList.cons 5 (NatList.cons 6 NatList.nil))))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate2.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate4".
idtac "Advanced".
idtac "Possible points: 1".
check_type @NatList.test_alternate4 (
(NatList.alternate NatList.nil
   (NatList.cons 20 (NatList.cons 30 NatList.nil)) =
 NatList.cons 20 (NatList.cons 30 NatList.nil))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate4.
Goal True.
idtac " ".

idtac "-------------------  bag_functions  --------------------".
idtac " ".

idtac "#> NatList.test_count2".
idtac "Possible points: 0.5".
check_type @NatList.test_count2 (
(NatList.count 6
   (NatList.cons 1
      (NatList.cons 2
         (NatList.cons 3
            (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))))) =
 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_count2.
Goal True.
idtac " ".

idtac "#> NatList.test_sum1".
idtac "Possible points: 0.5".
check_type @NatList.test_sum1 (
(NatList.count 1
   (NatList.sum
      (NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))
      (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))) = 3)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_sum1.
Goal True.
idtac " ".

idtac "#> NatList.test_add1".
idtac "Possible points: 0.5".
check_type @NatList.test_add1 (
(NatList.count 1
   (NatList.add 1
      (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))) = 3)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_add1.
Goal True.
idtac " ".

idtac "#> NatList.test_add2".
idtac "Possible points: 0.5".
check_type @NatList.test_add2 (
(NatList.count 5
   (NatList.add 1
      (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))) = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_add2.
Goal True.
idtac " ".

idtac "#> NatList.test_member1".
idtac "Possible points: 0.5".
check_type @NatList.test_member1 (
(NatList.member 1
   (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil))) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_member1.
Goal True.
idtac " ".

idtac "#> NatList.test_member2".
idtac "Possible points: 0.5".
check_type @NatList.test_member2 (
(NatList.member 2
   (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil))) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_member2.
Goal True.
idtac " ".

idtac "-------------------  bag_theorem  --------------------".
idtac " ".

idtac "#> Manually graded: bag_theorem".
idtac "Possible points: 3".
print_manual_grade score_bag_theorem.
idtac " ".

idtac "-------------------  list_exercises  --------------------".
idtac " ".

idtac "#> NatList.app_nil_r".
idtac "Possible points: 0.5".
check_type @NatList.app_nil_r (
(forall l : NatList.natlist, NatList.app l NatList.nil = l)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.app_nil_r.
Goal True.
idtac " ".

idtac "#> NatList.rev_app_distr".
idtac "Possible points: 0.5".
check_type @NatList.rev_app_distr (
(forall l1 l2 : NatList.natlist,
 NatList.rev (NatList.app l1 l2) =
 NatList.app (NatList.rev l2) (NatList.rev l1))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.rev_app_distr.
Goal True.
idtac " ".

idtac "#> NatList.rev_involutive".
idtac "Possible points: 0.5".
check_type @NatList.rev_involutive (
(forall l : NatList.natlist, NatList.rev (NatList.rev l) = l)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.rev_involutive.
Goal True.
idtac " ".

idtac "#> NatList.app_assoc4".
idtac "Possible points: 0.5".
check_type @NatList.app_assoc4 (
(forall l1 l2 l3 l4 : NatList.natlist,
 NatList.app l1 (NatList.app l2 (NatList.app l3 l4)) =
 NatList.app (NatList.app (NatList.app l1 l2) l3) l4)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.app_assoc4.
Goal True.
idtac " ".

idtac "#> NatList.nonzeros_app".
idtac "Possible points: 1".
check_type @NatList.nonzeros_app (
(forall l1 l2 : NatList.natlist,
 NatList.nonzeros (NatList.app l1 l2) =
 NatList.app (NatList.nonzeros l1) (NatList.nonzeros l2))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.nonzeros_app.
Goal True.
idtac " ".

idtac "-------------------  beq_natlist  --------------------".
idtac " ".

idtac "#> NatList.beq_natlist_refl".
idtac "Possible points: 2".
check_type @NatList.beq_natlist_refl (
(forall l : NatList.natlist, true = NatList.beq_natlist l l)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.beq_natlist_refl.
Goal True.
idtac " ".

idtac "-------------------  count_member_nonzero  --------------------".
idtac " ".

idtac "#> NatList.count_member_nonzero".
idtac "Possible points: 1".
check_type @NatList.count_member_nonzero (
(forall s : NatList.bag, leb 1 (NatList.count 1 (NatList.cons 1 s)) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.count_member_nonzero.
Goal True.
idtac " ".

idtac "-------------------  remove_decreases_count  --------------------".
idtac " ".

idtac "#> NatList.remove_decreases_count".
idtac "Advanced".
idtac "Possible points: 3".
check_type @NatList.remove_decreases_count (
(forall s : NatList.bag,
 leb (NatList.count 0 (NatList.remove_one 0 s)) (NatList.count 0 s) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.remove_decreases_count.
Goal True.
idtac " ".

idtac "-------------------  rev_injective  --------------------".
idtac " ".

idtac "#> Manually graded: rev_injective".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_rev_injective.
idtac " ".

idtac "-------------------  hd_error  --------------------".
idtac " ".

idtac "#> NatList.hd_error".
idtac "Possible points: 2".
check_type @NatList.hd_error ((NatList.natlist -> NatList.natoption)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.hd_error.
Goal True.
idtac " ".

idtac "-------------------  beq_id_refl  --------------------".
idtac " ".

idtac "#> beq_id_refl".
idtac "Possible points: 1".
check_type @beq_id_refl ((forall x : id, true = beq_id x x)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_id_refl.
Goal True.
idtac " ".

idtac "-------------------  update_eq  --------------------".
idtac " ".

idtac "#> PartialMap.update_eq".
idtac "Possible points: 1".
check_type @PartialMap.update_eq (
(forall (d : PartialMap.partial_map) (x : id) (v : nat),
 PartialMap.find x (PartialMap.update d x v) = NatList.Some v)).
idtac "Assumptions:".
Abort.
Print Assumptions PartialMap.update_eq.
Goal True.
idtac " ".

idtac "-------------------  update_neq  --------------------".
idtac " ".

idtac "#> PartialMap.update_neq".
idtac "Possible points: 1".
check_type @PartialMap.update_neq (
(forall (d : PartialMap.partial_map) (x y : id) (o : nat),
 beq_id x y = false ->
 PartialMap.find x (PartialMap.update d y o) = PartialMap.find x d)).
idtac "Assumptions:".
Abort.
Print Assumptions PartialMap.update_neq.
Goal True.
idtac " ".

idtac "-------------------  baz_num_elts  --------------------".
idtac " ".

idtac "#> Manually graded: baz_num_elts".
idtac "Possible points: 2".
print_manual_grade score_baz_num_elts.
idtac " ".

idtac " ".

idtac "Max points - standard: 22".
idtac "Max points - advanced: 32".
Abort.
