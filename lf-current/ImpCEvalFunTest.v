Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import ImpCEvalFun.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import ImpCEvalFun.
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
print_manual_grade manual_grade_for_ceval_step__ceval_inf.
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
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- pup_to_n ---------".
Print Assumptions pup_to_n.
idtac "---------- ceval_step__ceval_inf ---------".
idtac "MANUAL".
idtac "---------- ceval__ceval_step ---------".
Print Assumptions ceval__ceval_step.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:32:37 UTC 2019 *)
