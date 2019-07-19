Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Stlc.

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

From PLF Require Import Stlc.
Import Check.

Goal True.

idtac "-------------------  substi_correct  --------------------".
idtac " ".

idtac "#> STLC.substi_correct".
idtac "Possible points: 3".
check_type @STLC.substi_correct (
(forall (s : STLC.tm) (x : String.string) (t t' : STLC.tm),
 STLC.subst x s t = t' <-> STLC.substi s x t t')).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.substi_correct.
Goal True.
idtac " ".

idtac "-------------------  step_example5  --------------------".
idtac " ".

idtac "#> STLC.step_example5".
idtac "Possible points: 2".
check_type @STLC.step_example5 (
(STLC.multistep (STLC.app (STLC.app STLC.idBBBB STLC.idBB) STLC.idB) STLC.idB)).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.step_example5.
Goal True.
idtac " ".

idtac "-------------------  typing_example_3  --------------------".
idtac " ".

idtac "#> STLC.typing_example_3".
idtac "Possible points: 2".
check_type @STLC.typing_example_3 (
(exists T : STLC.ty,
   STLC.has_type (@Maps.empty STLC.ty)
     (STLC.abs STLC.x (STLC.Arrow STLC.Bool STLC.Bool)
        (STLC.abs STLC.y (STLC.Arrow STLC.Bool STLC.Bool)
           (STLC.abs STLC.z STLC.Bool
              (STLC.app (STLC.var STLC.y)
                 (STLC.app (STLC.var STLC.x) (STLC.var STLC.z)))))) T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.typing_example_3.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- STLC.substi_correct ---------".
Print Assumptions STLC.substi_correct.
idtac "---------- STLC.step_example5 ---------".
Print Assumptions STLC.step_example5.
idtac "---------- STLC.typing_example_3 ---------".
Print Assumptions STLC.typing_example_3.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:33:37 UTC 2019 *)
