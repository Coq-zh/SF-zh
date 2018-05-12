Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
Require Import Records.
Parameter MISSING: Type. 

Module Check. 

Ltac check_type A B := 
match type of A with 
| context[MISSING] => idtac "Missing:" A  
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"] 
end. 

Ltac print_manual_grade A := 
match eval compute in A with 
| Some (pair ?S ?C) => 
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

Require Import Records.
Import Check.

Goal True.

idtac "-------------------  examples  --------------------".
idtac " ".

idtac "#> STLCExtendedRecords.typing_example_2".
idtac "Possible points: 0.5".
check_type @STLCExtendedRecords.typing_example_2 (
(STLCExtendedRecords.has_type (@Maps.empty STLCExtendedRecords.ty)
   (STLCExtendedRecords.tapp
      (STLCExtendedRecords.tabs "a"
         (STLCExtendedRecords.TRCons "i1"
            (STLCExtendedRecords.TArrow STLCExtendedRecords.A
               STLCExtendedRecords.A)
            (STLCExtendedRecords.TRCons "i2"
               (STLCExtendedRecords.TArrow STLCExtendedRecords.B
                  STLCExtendedRecords.B) STLCExtendedRecords.TRNil))
         (STLCExtendedRecords.tproj (STLCExtendedRecords.tvar "a") "i2"))
      (STLCExtendedRecords.trcons "i1"
         (STLCExtendedRecords.tabs "a" STLCExtendedRecords.A
            (STLCExtendedRecords.tvar "a"))
         (STLCExtendedRecords.trcons "i2"
            (STLCExtendedRecords.tabs "a" STLCExtendedRecords.B
               (STLCExtendedRecords.tvar "a")) STLCExtendedRecords.trnil)))
   (STLCExtendedRecords.TArrow STLCExtendedRecords.B STLCExtendedRecords.B))).
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
         (STLCExtendedRecords.TRCons "i2"
            (STLCExtendedRecords.TArrow STLCExtendedRecords.A
               STLCExtendedRecords.A) STLCExtendedRecords.TRNil))
      (STLCExtendedRecords.trcons "i1"
         (STLCExtendedRecords.tabs "a" STLCExtendedRecords.B
            (STLCExtendedRecords.tvar "a")) (STLCExtendedRecords.tvar "a")) T))).
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
      (STLCExtendedRecords.tapp
         (STLCExtendedRecords.tabs "a"
            (STLCExtendedRecords.TRCons "i1" STLCExtendedRecords.A
               STLCExtendedRecords.TRNil)
            (STLCExtendedRecords.tproj (STLCExtendedRecords.tvar "a") "i1"))
         (STLCExtendedRecords.trcons "i1" (STLCExtendedRecords.tvar y)
            (STLCExtendedRecords.trcons "i2" (STLCExtendedRecords.tvar y)
               STLCExtendedRecords.trnil))) T))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample_2.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 2".
idtac "Max points - advanced: 2".
Abort.
