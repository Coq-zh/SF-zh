Set Warnings "-notation-overridden,-parsing".
Require Import Poly.
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

Require Import Poly.
Import Check.

Goal True.

idtac "-------------------  mumble_grumble  --------------------".
idtac " ".

idtac "#> Manually graded: mumble_grumble".
idtac "Possible points: 2".
print_manual_grade score_mumble_grumble.
idtac " ".

idtac "-------------------  split  --------------------".
idtac " ".

idtac "#> split".
idtac "Possible points: 1".
check_type @split ((forall X Y : Type, list (X * Y) -> list X * list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions split.
Goal True.
idtac " ".

idtac "#> test_split".
idtac "Possible points: 1".
check_type @test_split (
(@split nat bool [(1, false); (2, false)] = ([1; 2], [false; false]))).
idtac "Assumptions:".
Abort.
Print Assumptions test_split.
Goal True.
idtac " ".

idtac "-------------------  filter_even_gt7  --------------------".
idtac " ".

idtac "#> test_filter_even_gt7_1".
idtac "Possible points: 1".
check_type @test_filter_even_gt7_1 (
(filter_even_gt7 [1; 2; 6; 9; 10; 3; 12; 8] = [10; 12; 8])).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_1.
Goal True.
idtac " ".

idtac "#> test_filter_even_gt7_2".
idtac "Possible points: 1".
check_type @test_filter_even_gt7_2 ((filter_even_gt7 [5; 2; 6; 19; 129] = [ ])).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_2.
Goal True.
idtac " ".

idtac "-------------------  partition  --------------------".
idtac " ".

idtac "#> partition".
idtac "Possible points: 1".
check_type @partition ((forall X : Type, (X -> bool) -> list X -> list X * list X)).
idtac "Assumptions:".
Abort.
Print Assumptions partition.
Goal True.
idtac " ".

idtac "#> test_partition1".
idtac "Possible points: 1".
check_type @test_partition1 ((@partition nat oddb [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4]))).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition1.
Goal True.
idtac " ".

idtac "#> test_partition2".
idtac "Possible points: 1".
check_type @test_partition2 (
(@partition nat (fun _ : nat => false) [5; 9; 0] = ([ ], [5; 9; 0]))).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition2.
Goal True.
idtac " ".

idtac "-------------------  map_rev  --------------------".
idtac " ".

idtac "#> map_rev".
idtac "Possible points: 3".
check_type @map_rev (
(forall (X Y : Type) (f : X -> Y) (l : list X),
 @map X Y f (@rev X l) = @rev Y (@map X Y f l))).
idtac "Assumptions:".
Abort.
Print Assumptions map_rev.
Goal True.
idtac " ".

idtac "-------------------  flat_map  --------------------".
idtac " ".

idtac "#> flat_map".
idtac "Possible points: 1".
check_type @flat_map ((forall X Y : Type, (X -> list Y) -> list X -> list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions flat_map.
Goal True.
idtac " ".

idtac "#> test_flat_map1".
idtac "Possible points: 1".
check_type @test_flat_map1 (
(@flat_map nat nat (fun n : nat => [n; n; n]) [1; 5; 4] =
 [1; 1; 1; 5; 5; 5; 4; 4; 4])).
idtac "Assumptions:".
Abort.
Print Assumptions test_flat_map1.
Goal True.
idtac " ".

idtac "-------------------  fold_types_different  --------------------".
idtac " ".

idtac "#> Manually graded: fold_types_different".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade score_fold_types_different.
idtac " ".

idtac "-------------------  fold_length  --------------------".
idtac " ".

idtac "#> Exercises.fold_length_correct".
idtac "Possible points: 2".
check_type @Exercises.fold_length_correct (
(forall (X : Type) (l : list X), @Exercises.fold_length X l = @length X l)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.fold_length_correct.
Goal True.
idtac " ".

idtac "-------------------  fold_map  --------------------".
idtac " ".

idtac "#> Manually graded: fold_map".
idtac "Possible points: 3".
print_manual_grade score_fold_map.
idtac " ".

idtac "-------------------  currying  --------------------".
idtac " ".

idtac "#> Exercises.uncurry_curry".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.uncurry_curry (
(forall (X Y Z : Type) (f : X -> Y -> Z) (x : X) (y : Y),
 @Exercises.prod_curry X Y Z (@Exercises.prod_uncurry X Y Z f) x y = f x y)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.uncurry_curry.
Goal True.
idtac " ".

idtac "#> Exercises.curry_uncurry".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.curry_uncurry (
(forall (X Y Z : Type) (f : X * Y -> Z) (p : X * Y),
 @Exercises.prod_uncurry X Y Z (@Exercises.prod_curry X Y Z f) p = f p)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.curry_uncurry.
Goal True.
idtac " ".

idtac "-------------------  nth_error_informal  --------------------".
idtac " ".

idtac "#> Manually graded: nth_error_informal".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade score_nth_error_informal.
idtac " ".

idtac "-------------------  church_numerals  --------------------".
idtac " ".

idtac "#> Manually graded: church_numerals".
idtac "Advanced".
idtac "Possible points: 4".
print_manual_grade score_church_numerals.
idtac " ".

idtac " ".

idtac "Max points - standard: 19".
idtac "Max points - advanced: 28".
Abort.
