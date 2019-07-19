Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import MoreStlc.

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

From PLF Require Import MoreStlc.
Import Check.

Goal True.

idtac "-------------------  STLCE_definitions  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.extensions_definition".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_extensions_definition.
idtac " ".

idtac "-------------------  STLCE_examples  --------------------".
idtac " ".

idtac "#> STLCExtended.Examples.Prodtest.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.Prodtest.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.Prodtest.test STLCExtended.Nat)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.Prodtest.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.Prodtest.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.Prodtest.reduces (
(STLCExtended.multistep STLCExtended.Examples.Prodtest.test
   (STLCExtended.const 6))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.Prodtest.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.LetTest.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.LetTest.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.LetTest.test STLCExtended.Nat)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.LetTest.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.LetTest.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.LetTest.reduces (
(STLCExtended.multistep STLCExtended.Examples.LetTest.test
   (STLCExtended.const 6))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.LetTest.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest1.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest1.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest1.fact
   (STLCExtended.Arrow STLCExtended.Nat STLCExtended.Nat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest1.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest1.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest1.reduces (
(STLCExtended.multistep
   (STLCExtended.app STLCExtended.Examples.FixTest1.fact
      (STLCExtended.const 4)) (STLCExtended.const 24))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest1.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest2.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest2.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest2.map
   (STLCExtended.Arrow (STLCExtended.Arrow STLCExtended.Nat STLCExtended.Nat)
      (STLCExtended.Arrow (STLCExtended.List STLCExtended.Nat)
         (STLCExtended.List STLCExtended.Nat))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest2.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest2.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest2.reduces (
(STLCExtended.multistep
   (STLCExtended.app
      (STLCExtended.app STLCExtended.Examples.FixTest2.map
         (STLCExtended.abs STLCExtended.Examples.a STLCExtended.Nat
            (STLCExtended.scc (STLCExtended.var STLCExtended.Examples.a))))
      (STLCExtended.tcons (STLCExtended.const 1)
         (STLCExtended.tcons (STLCExtended.const 2)
            (STLCExtended.tnil STLCExtended.Nat))))
   (STLCExtended.tcons (STLCExtended.const 2)
      (STLCExtended.tcons (STLCExtended.const 3)
         (STLCExtended.tnil STLCExtended.Nat))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest2.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest3.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest3.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest3.equal
   (STLCExtended.Arrow STLCExtended.Nat
      (STLCExtended.Arrow STLCExtended.Nat STLCExtended.Nat)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest3.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest3.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest3.reduces (
(STLCExtended.multistep
   (STLCExtended.app
      (STLCExtended.app STLCExtended.Examples.FixTest3.equal
         (STLCExtended.const 4)) (STLCExtended.const 4))
   (STLCExtended.const 1))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest3.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest4.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest4.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest4.eotest
   (STLCExtended.Prod STLCExtended.Nat STLCExtended.Nat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest4.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest4.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest4.reduces (
(STLCExtended.multistep STLCExtended.Examples.FixTest4.eotest
   (STLCExtended.pair (STLCExtended.const 0) (STLCExtended.const 1)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest4.reduces.
Goal True.
idtac " ".

idtac "-------------------  STLCE_progress  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.progress".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_progress.
idtac " ".

idtac "-------------------  STLCE_context_invariance  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.context_invariance".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_context_invariance.
idtac " ".

idtac "-------------------  STLCE_subst_preserves_typing  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.substitution_preserves_typing".
idtac "Possible points: 2".
print_manual_grade STLCExtended.manual_grade_for_substitution_preserves_typing.
idtac " ".

idtac "-------------------  STLCE_preservation  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.preservation".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_preservation.
idtac " ".

idtac " ".

idtac "Max points - standard: 17".
idtac "Max points - advanced: 17".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- extensions_definition ---------".
idtac "MANUAL".
idtac "---------- STLCExtended.Examples.Prodtest.typechecks ---------".
Print Assumptions STLCExtended.Examples.Prodtest.typechecks.
idtac "---------- STLCExtended.Examples.Prodtest.reduces ---------".
Print Assumptions STLCExtended.Examples.Prodtest.reduces.
idtac "---------- STLCExtended.Examples.LetTest.typechecks ---------".
Print Assumptions STLCExtended.Examples.LetTest.typechecks.
idtac "---------- STLCExtended.Examples.LetTest.reduces ---------".
Print Assumptions STLCExtended.Examples.LetTest.reduces.
idtac "---------- STLCExtended.Examples.FixTest1.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest1.typechecks.
idtac "---------- STLCExtended.Examples.FixTest1.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest1.reduces.
idtac "---------- STLCExtended.Examples.FixTest2.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest2.typechecks.
idtac "---------- STLCExtended.Examples.FixTest2.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest2.reduces.
idtac "---------- STLCExtended.Examples.FixTest3.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest3.typechecks.
idtac "---------- STLCExtended.Examples.FixTest3.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest3.reduces.
idtac "---------- STLCExtended.Examples.FixTest4.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest4.typechecks.
idtac "---------- STLCExtended.Examples.FixTest4.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest4.reduces.
idtac "---------- progress ---------".
idtac "MANUAL".
idtac "---------- context_invariance ---------".
idtac "MANUAL".
idtac "---------- substitution_preserves_typing ---------".
idtac "MANUAL".
idtac "---------- preservation ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* Fri Jul 19 00:33:47 UTC 2019 *)
