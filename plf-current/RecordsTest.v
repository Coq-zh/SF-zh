Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Records.

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

From PLF Require Import Records.
Import Check.

Goal True.

idtac "-------------------  examples  --------------------".
idtac " ".

idtac "#> STLCExtendedRecords.typing_example_2".
idtac "Possible points: 0.5".
check_type @STLCExtendedRecords.typing_example_2 (
(STLCExtendedRecords.has_type (@Maps.empty STLCExtendedRecords.ty)
   (STLCExtendedRecords.app
      (STLCExtendedRecords.abs "a"
         (STLCExtendedRecords.RCons "i1"
            (STLCExtendedRecords.Arrow STLCExtendedRecords.A
               STLCExtendedRecords.A)
            (STLCExtendedRecords.RCons "i2"
               (STLCExtendedRecords.Arrow STLCExtendedRecords.B
                  STLCExtendedRecords.B) STLCExtendedRecords.RNil))
         (STLCExtendedRecords.rproj (STLCExtendedRecords.var "a") "i2"))
      (STLCExtendedRecords.rcons "i1"
         (STLCExtendedRecords.abs "a" STLCExtendedRecords.A
            (STLCExtendedRecords.var "a"))
         (STLCExtendedRecords.rcons "i2"
            (STLCExtendedRecords.abs "a" STLCExtendedRecords.B
               (STLCExtendedRecords.var "a")) STLCExtendedRecords.trnil)))
   (STLCExtendedRecords.Arrow STLCExtendedRecords.B STLCExtendedRecords.B))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_example_2.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_nonexample".
idtac "Possible points: 0.5".
check_type @STLCExtendedRecords.typing_nonexample (
(~
 (exists T : STLCExtendedRecords.ty,
    STLCExtendedRecords.has_type
      (@Maps.update STLCExtendedRecords.ty
         (@Maps.empty STLCExtendedRecords.ty) "a"
         (STLCExtendedRecords.RCons "i2"
            (STLCExtendedRecords.Arrow STLCExtendedRecords.A
               STLCExtendedRecords.A) STLCExtendedRecords.RNil))
      (STLCExtendedRecords.rcons "i1"
         (STLCExtendedRecords.abs "a" STLCExtendedRecords.B
            (STLCExtendedRecords.var "a")) (STLCExtendedRecords.var "a")) T))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_nonexample_2".
idtac "Possible points: 1".
check_type @STLCExtendedRecords.typing_nonexample_2 (
(forall y : String.string,
 ~
 (exists T : STLCExtendedRecords.ty,
    STLCExtendedRecords.has_type
      (@Maps.update STLCExtendedRecords.ty
         (@Maps.empty STLCExtendedRecords.ty) y STLCExtendedRecords.A)
      (STLCExtendedRecords.app
         (STLCExtendedRecords.abs "a"
            (STLCExtendedRecords.RCons "i1" STLCExtendedRecords.A
               STLCExtendedRecords.RNil)
            (STLCExtendedRecords.rproj (STLCExtendedRecords.var "a") "i1"))
         (STLCExtendedRecords.rcons "i1" (STLCExtendedRecords.var y)
            (STLCExtendedRecords.rcons "i2" (STLCExtendedRecords.var y)
               STLCExtendedRecords.trnil))) T))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample_2.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 2".
idtac "Max points - advanced: 2".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- STLCExtendedRecords.typing_example_2 ---------".
Print Assumptions STLCExtendedRecords.typing_example_2.
idtac "---------- STLCExtendedRecords.typing_nonexample ---------".
Print Assumptions STLCExtendedRecords.typing_nonexample.
idtac "---------- STLCExtendedRecords.typing_nonexample_2 ---------".
Print Assumptions STLCExtendedRecords.typing_nonexample_2.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-04-03 05:23:03 (UTC+00) *)
