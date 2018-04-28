Set Warnings "-notation-overridden,-parsing".
Require Import Logic.
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

Require Import Logic.
Import Check.

Goal True.

idtac "-------------------  and_exercise  --------------------".
idtac " ".

idtac "#> and_exercise".
idtac "Possible points: 2".
check_type @and_exercise ((forall n m : nat, n + m = 0 -> n = 0 /\ m = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions and_exercise.
Goal True.
idtac " ".

idtac "-------------------  and_assoc  --------------------".
idtac " ".

idtac "#> and_assoc".
idtac "Possible points: 2".
check_type @and_assoc ((forall P Q R : Prop, P /\ Q /\ R -> (P /\ Q) /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "-------------------  mult_eq_0  --------------------".
idtac " ".

idtac "#> mult_eq_0".
idtac "Possible points: 1".
check_type @mult_eq_0 ((forall n m : nat, n * m = 0 -> n = 0 \/ m = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_eq_0.
Goal True.
idtac " ".

idtac "-------------------  or_commut  --------------------".
idtac " ".

idtac "#> or_commut".
idtac "Possible points: 1".
check_type @or_commut ((forall P Q : Prop, P \/ Q -> Q \/ P)).
idtac "Assumptions:".
Abort.
Print Assumptions or_commut.
Goal True.
idtac " ".

idtac "-------------------  double_neg_inf  --------------------".
idtac " ".

idtac "#> Manually graded: double_neg_inf".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade score_double_neg_inf.
idtac " ".

idtac "-------------------  contrapositive  --------------------".
idtac " ".

idtac "#> contrapositive".
idtac "Possible points: 2".
check_type @contrapositive ((forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions contrapositive.
Goal True.
idtac " ".

idtac "-------------------  not_both_true_and_false  --------------------".
idtac " ".

idtac "#> not_both_true_and_false".
idtac "Possible points: 1".
check_type @not_both_true_and_false ((forall P : Prop, ~ (P /\ ~ P))).
idtac "Assumptions:".
Abort.
Print Assumptions not_both_true_and_false.
Goal True.
idtac " ".

idtac "-------------------  informal_not_PNP  --------------------".
idtac " ".

idtac "#> Manually graded: informal_not_PNP".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade score_informal_not_PNP.
idtac " ".

idtac "-------------------  or_distributes_over_and  --------------------".
idtac " ".

idtac "#> or_distributes_over_and".
idtac "Possible points: 3".
check_type @or_distributes_over_and (
(forall P Q R : Prop, P \/ Q /\ R <-> (P \/ Q) /\ (P \/ R))).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and.
Goal True.
idtac " ".

idtac "-------------------  dist_not_exists  --------------------".
idtac " ".

idtac "#> dist_not_exists".
idtac "Possible points: 1".
check_type @dist_not_exists (
(forall (X : Type) (P : X -> Prop),
 (forall x : X, P x) -> ~ (exists x : X, ~ P x))).
idtac "Assumptions:".
Abort.
Print Assumptions dist_not_exists.
Goal True.
idtac " ".

idtac "-------------------  dist_exists_or  --------------------".
idtac " ".

idtac "#> dist_exists_or".
idtac "Possible points: 2".
check_type @dist_exists_or (
(forall (X : Type) (P Q : X -> Prop),
 (exists x : X, P x \/ Q x) <-> (exists x : X, P x) \/ (exists x : X, Q x))).
idtac "Assumptions:".
Abort.
Print Assumptions dist_exists_or.
Goal True.
idtac " ".

idtac "-------------------  In_map_iff  --------------------".
idtac " ".

idtac "#> In_map_iff".
idtac "Possible points: 2".
check_type @In_map_iff (
(forall (A B : Type) (f : A -> B) (l : list A) (y : B),
 @In B y (@map A B f l) <-> (exists x : A, f x = y /\ @In A x l))).
idtac "Assumptions:".
Abort.
Print Assumptions In_map_iff.
Goal True.
idtac " ".

idtac "-------------------  In_app_iff  --------------------".
idtac " ".

idtac "#> In_app_iff".
idtac "Possible points: 2".
check_type @In_app_iff (
(forall (A : Type) (l l' : list A) (a : A),
 @In A a (l ++ l') <-> @In A a l \/ @In A a l')).
idtac "Assumptions:".
Abort.
Print Assumptions In_app_iff.
Goal True.
idtac " ".

idtac "-------------------  All  --------------------".
idtac " ".

idtac "#> All".
idtac "Possible points: 3".
check_type @All ((forall T : Type, (T -> Prop) -> list T -> Prop)).
idtac "Assumptions:".
Abort.
Print Assumptions All.
Goal True.
idtac " ".

idtac "-------------------  combine_odd_even  --------------------".
idtac " ".

idtac "#> combine_odd_even".
idtac "Possible points: 3".
check_type @combine_odd_even (((nat -> Prop) -> (nat -> Prop) -> nat -> Prop)).
idtac "Assumptions:".
Abort.
Print Assumptions combine_odd_even.
Goal True.
idtac " ".

idtac "-------------------  tr_rev_correct  --------------------".
idtac " ".

idtac "#> tr_rev_correct".
idtac "Possible points: 4".
check_type @tr_rev_correct ((forall X : Type, @tr_rev X = @rev X)).
idtac "Assumptions:".
Abort.
Print Assumptions tr_rev_correct.
Goal True.
idtac " ".

idtac "-------------------  evenb_double_conv  --------------------".
idtac " ".

idtac "#> evenb_double_conv".
idtac "Possible points: 3".
check_type @evenb_double_conv (
(forall n : nat,
 exists k : nat, n = (if evenb n then double k else S (double k)))).
idtac "Assumptions:".
Abort.
Print Assumptions evenb_double_conv.
Goal True.
idtac " ".

idtac "-------------------  logical_connectives  --------------------".
idtac " ".

idtac "#> andb_true_iff".
idtac "Possible points: 1".
check_type @andb_true_iff (
(forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_iff.
Goal True.
idtac " ".

idtac "#> orb_true_iff".
idtac "Possible points: 1".
check_type @orb_true_iff (
(forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true)).
idtac "Assumptions:".
Abort.
Print Assumptions orb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  beq_nat_false_iff  --------------------".
idtac " ".

idtac "#> beq_nat_false_iff".
idtac "Possible points: 1".
check_type @beq_nat_false_iff ((forall x y : nat, beq_nat x y = false <-> x <> y)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_false_iff.
Goal True.
idtac " ".

idtac "-------------------  beq_list  --------------------".
idtac " ".

idtac "#> beq_list".
idtac "Possible points: 3".
check_type @beq_list ((forall A : Type, (A -> A -> bool) -> list A -> list A -> bool)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_list.
Goal True.
idtac " ".

idtac "-------------------  All_forallb  --------------------".
idtac " ".

idtac "#> forallb_true_iff".
idtac "Possible points: 2".
check_type @forallb_true_iff (
(forall (X : Type) (test : X -> bool) (l : list X),
 @forallb X test l = true <-> @All X (fun x : X => test x = true) l)).
idtac "Assumptions:".
Abort.
Print Assumptions forallb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  excluded_middle_irrefutable  --------------------".
idtac " ".

idtac "#> excluded_middle_irrefutable".
idtac "Possible points: 3".
check_type @excluded_middle_irrefutable ((forall P : Prop, ~ ~ (P \/ ~ P))).
idtac "Assumptions:".
Abort.
Print Assumptions excluded_middle_irrefutable.
Goal True.
idtac " ".

idtac "-------------------  not_exists_dist  --------------------".
idtac " ".

idtac "#> not_exists_dist".
idtac "Advanced".
idtac "Possible points: 3".
check_type @not_exists_dist (
(excluded_middle ->
 forall (X : Type) (P : X -> Prop),
 ~ (exists x : X, ~ P x) -> forall x : X, P x)).
idtac "Assumptions:".
Abort.
Print Assumptions not_exists_dist.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 43".
idtac "Max points - advanced: 49".
Abort.
