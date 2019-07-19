(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, give us an algorithm for _checking_ whether or not a term
    is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)

(** This short chapter constructs such a function and proves it
    correct. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

(* ################################################################# *)
(** * Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | Bool, Bool =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [eqb_ty] and the logical
    proposition that its inputs are equal. *)

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1=Arrow T1_1 T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
End STLCTypes.

(* ################################################################# *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [Arrow T11 T12]
    for some [T11] and [T12]). *)

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      Gamma x
  | abs x T11 t12 =>
      match type_check (update Gamma x T11) t12 with
      | Some T12 => Some (Arrow T11 T12)
      | _ => None
      end
  | app t1 t2 =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some (Arrow T11 T12),Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | tru =>
      Some Bool
  | fls =>
      Some Bool
  | test guard t f =>
      match type_check Gamma guard with
      | Some Bool =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

End FirstTry.

(* ################################################################# *)
(** * Digression: Improving the Notation *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).
         
Notation " 'fail' "
  := None.

Module STLCChecker.
Import STLCTypes.

(** Now we can write the same type-checking function in a more
    imperative-looking style using these notations. *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | abs x T11 t12 =>
      T12 <- type_check (update Gamma x T11) t12 ;;
      return (Arrow T11 T12)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tru =>
      return Bool
  | fls =>
      return Bool
  | test guard t1 t2 =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | Bool =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ################################################################# *)
(** * Properties *)

(** To verify that the typechecking algorithm is correct, we show that
    it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H. 
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert; 
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma x0) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T11)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T)...
Qed.

End STLCChecker.

(* ################################################################# *)
(** * Exercises *)

(** **** 练习：5 星, standard (typechecker_extensions)  

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
(* 请勿修改下面这一行： *)
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
(* 请勿修改下面这一行： *)
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | Nat, Nat =>
      true
  | Unit, Unit =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Prod T11 T12, Prod T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Sum T11 T12, Sum T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | List T11, List T21 =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1.
  induction T1; simpl;
    try reflexivity;
    try (rewrite IHT1_1; rewrite IHT1_2; reflexivity);
    try (rewrite IHT1; reflexivity).  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | abs x1 T1 t2 =>
      T2 <- type_check (update Gamma x1 T1) t2 ;;
      return (Arrow T1 T2)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | const _ =>
      return Nat
  | scc t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | prd t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | mlt t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | Nat, Nat => return Nat
      | _,_        => fail
      end
  | test0 guard t f =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | Nat => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  (* 请在此处解答 *)
  (* lists (the [tlcase] is given for free) *)
  (* 请在此处解答 *)
  | tlcase t0 t1 x21 x22 t2 =>
      match type_check Gamma t0 with
      | Some (List T) =>
          match type_check Gamma t1,
                type_check (update (update Gamma x22 (List T)) x21 T) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then Some T1' else None
          | _,_ => None
          end
      | _ => None
      end
  (* unit *)
  (* 请在此处解答 *)
  (* pairs *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)
  | _ => None  (* ... and delete this line when you complete the exercise. *)
  end.

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|]; 
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H. 
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  (* 请在此处解答 *)
  - (* tlcase *)
    rename s into x31. rename s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (update (update Gamma x32 (List T11)) x31 T11) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  (* 请在此处解答 *)
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T)); 
    try (rewrite (eqb_ty_refl T1)); 
    try (rewrite (eqb_ty_refl T2)); 
    eauto.
  - destruct (Gamma x); try solve_by_invert. eauto.
  Admitted. (* ... and delete this line *)
(* 
Qed. (* ... and uncomment this one *)
*)
End TypecheckerExtensions.
(** [] *)

(** **** 练习：5 星, standard, optional (stlc_step_function)  

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a function [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof. (* 请在此处解答 *) Admitted.

(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof. (* 请在此处解答 *) Admitted.

End StepFunction.
(** [] *)

(** **** 练习：5 星, standard, optional (stlc_impl)  

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* 请在此处解答 *)
End StlcImpl.
(** [] *)

(* Fri Jul 19 00:33:15 UTC 2019 *)
