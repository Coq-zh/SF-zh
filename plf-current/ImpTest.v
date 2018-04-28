Set Warnings "-notation-overridden,-parsing".
Require Import Imp.
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

Require Import Imp.
Import Check.

Goal True.

idtac "-------------------  optimize_0plus_b_sound  --------------------".
idtac " ".

idtac "#> AExp.optimize_0plus_b_sound".
idtac "Possible points: 3".
check_type @AExp.optimize_0plus_b_sound (
(forall b : AExp.bexp, AExp.beval (AExp.optimize_0plus_b b) = AExp.beval b)).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.optimize_0plus_b_sound.
Goal True.
idtac " ".

idtac "-------------------  bevalR  --------------------".
idtac " ".

idtac "#> AExp.beval_iff_bevalR".
idtac "Possible points: 3".
check_type @AExp.beval_iff_bevalR (
(forall (b : AExp.bexp) (bv : bool), AExp.bevalR b bv <-> AExp.beval b = bv)).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.beval_iff_bevalR.
Goal True.
idtac " ".

idtac "-------------------  ceval_example2  --------------------".
idtac " ".

idtac "#> ceval_example2".
idtac "Possible points: 2".
check_type @ceval_example2 (
((X ::= 0;; Y ::= 1;; Z ::= 2) / @Maps.t_empty nat 0 \\
 {X --> 0; Y --> 1; Z --> 2})).
idtac "Assumptions:".
Abort.
Print Assumptions ceval_example2.
Goal True.
idtac " ".

idtac "-------------------  XtimesYinZ_spec  --------------------".
idtac " ".

idtac "#> Manually graded: XtimesYinZ_spec".
idtac "Possible points: 3".
print_manual_grade score_XtimesYinZ_spec.
idtac " ".

idtac "-------------------  loop_never_stops  --------------------".
idtac " ".

idtac "#> loop_never_stops".
idtac "Possible points: 3".
check_type @loop_never_stops ((forall st st' : state, ~ loop / st \\ st')).
idtac "Assumptions:".
Abort.
Print Assumptions loop_never_stops.
Goal True.
idtac " ".

idtac "-------------------  no_whiles_eqv  --------------------".
idtac " ".

idtac "#> no_whiles_eqv".
idtac "Possible points: 3".
check_type @no_whiles_eqv ((forall c : com, no_whiles c = true <-> no_whilesR c)).
idtac "Assumptions:".
Abort.
Print Assumptions no_whiles_eqv.
Goal True.
idtac " ".

idtac "-------------------  no_whiles_terminating  --------------------".
idtac " ".

idtac "#> Manually graded: no_whiles_terminating".
idtac "Possible points: 4".
print_manual_grade score_no_whiles_terminating.
idtac " ".

idtac "-------------------  stack_compiler  --------------------".
idtac " ".

idtac "#> s_execute1".
idtac "Possible points: 0.5".
check_type @s_execute1 (
(s_execute (@Maps.t_empty nat 0) (@nil nat)
   (SPush 5 :: (SPush 3 :: SPush 1 :: SMinus :: @nil sinstr)%list) =
 (2 :: 5 :: @nil nat)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute1.
Goal True.
idtac " ".

idtac "#> s_execute2".
idtac "Possible points: 0.5".
check_type @s_execute2 (
(s_execute {X --> 3} (3 :: (4 :: @nil nat)%list)
   (SPush 4 :: (SLoad X :: SMult :: SPlus :: @nil sinstr)%list) =
 (15 :: 4 :: @nil nat)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute2.
Goal True.
idtac " ".

idtac "#> s_compile1".
idtac "Possible points: 2".
check_type @s_compile1 (
(s_compile (X - 2 * Y) =
 (SLoad X :: SPush 2 :: SLoad Y :: SMult :: SMinus :: @nil sinstr)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile1.
Goal True.
idtac " ".

idtac "-------------------  stack_compiler_correct  --------------------".
idtac " ".

idtac "#> s_compile_correct".
idtac "Advanced".
idtac "Possible points: 4".
check_type @s_compile_correct (
(forall (st : state) (e : aexp),
 s_execute st (@nil nat) (s_compile e) = (aeval st e :: @nil nat)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile_correct.
Goal True.
idtac " ".

idtac "-------------------  break_imp  --------------------".
idtac " ".

idtac "#> BreakImp.break_ignore".
idtac "Advanced".
idtac "Possible points: 1".
check_type @BreakImp.break_ignore (
(forall (c : BreakImp.com) (st st' : state) (s : BreakImp.result),
 BreakImp.ceval (BreakImp.CSeq BreakImp.CBreak c) st s st' -> st = st')).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.break_ignore.
Goal True.
idtac " ".

idtac "#> BreakImp.while_continue".
idtac "Advanced".
idtac "Possible points: 1".
check_type @BreakImp.while_continue (
(forall (b : bexp) (c : BreakImp.com) (st st' : state) (s : BreakImp.result),
 BreakImp.ceval (BreakImp.CWhile b c) st s st' -> s = BreakImp.SContinue)).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.while_continue.
Goal True.
idtac " ".

idtac "#> BreakImp.while_stops_on_break".
idtac "Advanced".
idtac "Possible points: 2".
check_type @BreakImp.while_stops_on_break (
(forall (b : bexp) (c : BreakImp.com) (st st' : state),
 beval st b = true ->
 BreakImp.ceval c st BreakImp.SBreak st' ->
 BreakImp.ceval (BreakImp.CWhile b c) st BreakImp.SContinue st')).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.while_stops_on_break.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 24".
idtac "Max points - advanced: 32".
Abort.
