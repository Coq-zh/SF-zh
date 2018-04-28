Set Warnings "-notation-overridden,-parsing".
Require Import ImpCEvalFun.
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

Require Import ImpCEvalFun.
Import Check.

Goal True.

idtac "-------------------  pup_to_n  --------------------".
idtac " ".

idtac "#> pup_to_n".
idtac "Possible points: 2".
check_type @pup_to_n (Imp.com).
idtac "Assumptions:".
Abort.
Print Assumptions pup_to_n.
Goal True.
idtac " ".

idtac "-------------------  ceval_step__ceval_inf  --------------------".
idtac " ".

idtac "#> Manually graded: ceval_step__ceval_inf".
idtac "Possible points: 4".
print_manual_grade score_ceval_step__ceval_inf.
idtac " ".

idtac "-------------------  ceval__ceval_step  --------------------".
idtac " ".

idtac "#> ceval__ceval_step".
idtac "Possible points: 3".
check_type @ceval__ceval_step (
(forall (c : Imp.com) (st st' : Imp.state),
 Imp.ceval c st st' ->
 exists i : nat, ceval_step st c i = @Some Imp.state st')).
idtac "Assumptions:".
Abort.
Print Assumptions ceval__ceval_step.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 9".
idtac "Max points - advanced: 9".
Abort.
