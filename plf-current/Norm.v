(** * Norm: Normalization of STLC *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi.

(* Chapter written and maintained by Andrew Tolmach *)

(** This optional chapter is based on chapter 12 of _Types and
    Programming Languages_ (Pierce).  It may be useful to look at the
    two together, as that chapter includes explanations and informal
    proofs that are not repeated here.

    In this chapter, we consider another fundamental theoretical
    property of the simply typed lambda-calculus: the fact that the
    evaluation of a well-typed program is guaranteed to halt in a
    finite number of steps---i.e., every well-typed term is
    _normalizable_.

    Unlike the type-safety properties we have considered so far, the
    normalization property does not extend to full-blown programming
    languages, because these languages nearly always extend the simply
    typed lambda-calculus with constructs, such as general
    recursion (see the [MoreStlc] chapter) or recursive types, that
    can be used to write nonterminating programs.  However, the issue
    of normalization reappears at the level of _types_ when we
    consider the metatheory of polymorphic versions of the lambda
    calculus such as System F-omega: in this system, the language of
    types effectively contains a copy of the simply typed
    lambda-calculus, and the termination of the typechecking algorithm
    will hinge on the fact that a "normalization" operation on type
    expressions is guaranteed to terminate.

    Another reason for studying normalization proofs is that they are
    some of the most beautiful---and mind-blowing---mathematics to be
    found in the type theory literature, often (as here) involving the
    fundamental proof technique of _logical relations_.

    The calculus we shall consider here is the simply typed
    lambda-calculus over a single base type [bool] and with
    pairs. We'll give most details of the development for the basic
    lambda-calculus terms treating [bool] as an uninterpreted base
    type, and leave the extension to the boolean operators and pairs
    to the reader.  Even for the base calculus, normalization is not
    entirely trivial to prove, since each reduction of a term can
    duplicate redexes in subterms. *)

(** **** 练习：2 星, standard (norm_fail)  

    Where do we fail if we attempt to prove normalization by a
    straightforward induction on the size of a well-typed term? *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_norm_fail : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, standard, recommended (norm)  

    The best ways to understand an intricate proof like this is
    are (1) to help fill it in and (2) to extend it.  We've left out some
    parts of the following development, including some proofs of lemmas
    and the all the cases involving products and conditionals.  Fill them
    in. *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_norm : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Language *)

(** We begin by repeating the relevant language definition, which is
    similar to those in the [MoreStlc] chapter, plus supporting
    results including type preservation and step determinism.  (We
    won't need progress.)  You may just wish to skip down to the
    Normalization section... *)

(* ----------------------------------------------------------------- *)
(** *** Syntax and Operational Semantics *)

Inductive ty : Type :=
  | Bool : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.

Inductive tm : Type :=
    (* pure STLC *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
    (* pairs *)
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
    (* booleans *)
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
          (* i.e., [test t0 then t1 else t2] *)

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y => if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | pair t1 t2 => pair (subst x s t1) (subst x s t2)
  | fst t1 => fst (subst x s t1)
  | snd t1 => snd (subst x s t1)
  | tru => tru
  | fls => fls
  | test t0 t1 t2 =>
      test (subst x s t0) (subst x s t1) (subst x s t2)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (pair v1 v2)
  | v_tru : value tru
  | v_fls : value fls
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        (pair t1 t2) --> (pair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        (pair v1 t2) --> (pair v1 t2')
  | ST_Fst : forall t1 t1',
        t1 --> t1' ->
        (fst t1) --> (fst t1')
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (fst (pair v1 v2)) --> v1
  | ST_Snd : forall t1 t1',
        t1 --> t1' ->
        (snd t1) --> (snd t1')
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (snd (pair v1 v2)) --> v2
  (* booleans *)
  | ST_TestTrue : forall t1 t2,
        (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
        (test fls t1 t2) --> t2
  | ST_Test : forall t0 t0' t1 t2,
        t0 --> t0' ->
        (test t0 t1 t2) --> (test t0' t1 t2)

where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (update Gamma x T11) t12 T12 ->
      has_type Gamma (abs x T11 t12) (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      has_type Gamma t1 (Arrow T1 T2) ->
      has_type Gamma t2 T1 ->
      has_type Gamma (app t1 t2) T2
  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      has_type Gamma t1 T1 ->
      has_type Gamma t2 T2 ->
      has_type Gamma (pair t1 t2) (Prod T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      has_type Gamma t (Prod T1 T2) ->
      has_type Gamma (fst t) T1
  | T_Snd : forall Gamma t T1 T2,
      has_type Gamma t (Prod T1 T2) ->
      has_type Gamma (snd t) T2
  (* booleans *)
  | T_True : forall Gamma,
      has_type Gamma tru Bool
  | T_False : forall Gamma,
      has_type Gamma fls Bool
  | T_Test : forall Gamma t0 t1 t2 T,
      has_type Gamma t0 Bool ->
      has_type Gamma t1 T ->
      has_type Gamma t2 T ->
      has_type Gamma (test t0 t1 t2) T
.

Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

(* ----------------------------------------------------------------- *)
(** *** Context Invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (abs y T11 t12)
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (pair t1 t2)
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (pair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (fst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (snd t)
  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x (test t0 t1 t2)
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (test t0 t1 t2)
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (test t0 t1 t2)
.

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold update, t_update. destruct (eqb_stringP x y)...
  - (* T_Pair *)
    apply T_Pair...
  - (* T_Test *)
    eapply T_Test...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.

Corollary typable_empty__closed : forall t T,
    has_type empty t T  ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  inversion C.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (update Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma ([x:=v]t) S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then
     Gamma |- ([x:=v]t) S. *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of var and abs.
     The former aren't automatic because we must reason about how the
     variables interact. *)
  induction t;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  - (* var *)
    simpl. rename s into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [update Gamma x U y = Some S].  We want to
       show that [Gamma |- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    unfold update, t_update in H1.
    destruct (eqb_stringP x y).
    + (* x=y *)
    (* If [x = y], then we know that [U = S], and that [[x:=v]y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      subst.
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    + (* x<>y *)
      (* If [x <> y], then [Gamma y = Some S] and the substitution has no
         effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var...
  - (* abs *)
    rename s into y. rename t into T11.
    (* If [t = abs y T11 t0], then we know that
         [Gamma,x:U |- abs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma,
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 S].

       We can calculate that
         [x:=v]t = abs y T11 (if eqb_string x y then t0 else [x:=v]t0)
       And we must show that [Gamma |- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if eqb_string x y then t0 else [x:=v]t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    destruct (eqb_stringP x y).
    + (* x=y *)
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + (* x<>y *)
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- [x:=v]t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst. rewrite false_eqb_string...
Qed.

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t --> t'  ->
     has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t --> t'], then [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]).  We show just the interesting ones. *)
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t --> t']: [ST_App1], [ST_App2], and
       [ST_AppAbs]. In the first two cases, the result follows directly from
       the IH. *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      (* For the third case, suppose
           [t1 = abs x T11 t12]
         and
           [t2 = v2].
         We must show that [empty |- [x:=v2]t12 : T2].
         We know by assumption that
             [empty |- abs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  - (* T_Fst *)
    inversion HT...
  - (* T_Snd *)
    inversion HT...
Qed.

(* ----------------------------------------------------------------- *)
(** *** Determinism *)

Lemma step_deterministic :
   deterministic step.
Proof with eauto.
   unfold deterministic.
   intros t t' t'' E1 E2.
   generalize dependent t''.
   induction E1; intros t'' E2; inversion E2; subst; clear E2...
  (* ST_AppAbs *)
   - inversion H3.
   - exfalso; apply value__normal in H...
   (* ST_App1 *)
   - inversion E1.
   -  f_equal...
   - exfalso; apply value__normal in H1...
   (* ST_App2 *)
   - exfalso; apply value__normal in H3...
   - exfalso; apply value__normal in H...
   - f_equal...
   (* ST_Pair1 *)
   - f_equal...
   - exfalso; apply value__normal in H1...
   (* ST_Pair2 *)
   - exfalso; apply value__normal in H...
   - f_equal...
   (* ST_Fst *)
   - f_equal...
   - exfalso.
     inversion E1; subst.
     + apply value__normal in H0...
     + apply value__normal in H1...
   (* ST_FstPair *)
   - exfalso.
     inversion H2; subst.
     + apply value__normal in H...
     + apply value__normal in H0...
   (* ST_Snd *)
   - f_equal...
   - exfalso.
     inversion E1; subst.
     + apply value__normal in H0...
     + apply value__normal in H1...
   (* ST_SndPair *)
   - exfalso.
     inversion H2; subst.
     + apply value__normal in H...
     + apply value__normal in H0...
   - (* ST_TestTrue *)
       inversion H3.
   - (* ST_TestFalse *)
       inversion H3.
   (* ST_Test *)
   - inversion E1.
   - inversion E1.
   - f_equal...
Qed.

(* ################################################################# *)
(** * Normalization *)

(** Now for the actual normalization proof.

    Our goal is to prove that every well-typed term reduces to a
    normal form.  In fact, it turns out to be convenient to prove
    something slightly stronger, namely that every well-typed term
    reduces to a _value_.  This follows from the weaker property
    anyway via Progress (why?) but otherwise we don't need Progress,
    and we didn't bother re-proving it above.

    Here's the key definition: *)

Definition halts  (t:tm) : Prop :=  exists t', t -->* t' /\  value t'.

(** A trivial fact: *)

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  apply multi_refl.
  assumption.
Qed.

(** The key issue in the normalization proof (as in many proofs by
    induction) is finding a strong enough induction hypothesis.  To
    this end, we begin by defining, for each type [T], a set [R_T] of
    closed terms of type [T].  We will specify these sets using a
    relation [R] and write [R T t] when [t] is in [R_T]. (The sets
    [R_T] are sometimes called _saturated sets_ or _reducibility
    candidates_.)

    Here is the definition of [R] for the base language:

    - [R bool t] iff [t] is a closed term of type [bool] and [t] halts
      in a value

    - [R (T1 -> T2) t] iff [t] is a closed term of type [T1 -> T2] and
      [t] halts in a value _and_ for any term [s] such that [R T1 s],
      we have [R T2 (t s)]. *)

(** This definition gives us the strengthened induction hypothesis that we
    need.  Our primary goal is to show that all _programs_ ---i.e., all
    closed terms of base type---halt.  But closed terms of base type can
    contain subterms of functional type, so we need to know something
    about these as well.  Moreover, it is not enough to know that these
    subterms halt, because the application of a normalized function to a
    normalized argument involves a substitution, which may enable more
    reduction steps.  So we need a stronger condition for terms of
    functional type: not only should they halt themselves, but, when
    applied to halting arguments, they should yield halting results.

    The form of [R] is characteristic of the _logical relations_ proof
    technique.  (Since we are just dealing with unary relations here, we
    could perhaps more properly say _logical properties_.)  If we want to
    prove some property [P] of all closed terms of type [A], we proceed by
    proving, by induction on types, that all terms of type [A] _possess_
    property [P], all terms of type [A->A] _preserve_ property [P], all
    terms of type [(A->A)->(A->A)] _preserve the property of preserving_
    property [P], and so on.  We do this by defining a family of
    properties, indexed by types.  For the base type [A], the property is
    just [P].  For functional types, it says that the function should map
    values satisfying the property at the input type to values satisfying
    the property at the output type.

    When we come to formalize the definition of [R] in Coq, we hit a
    problem.  The most obvious formulation would be as a parameterized
    Inductive proposition like this:

      Inductive R : ty -> tm -> Prop :=
      | R_bool : forall b t, has_type empty t Bool ->
                      halts t ->
                      R Bool t
      | R_arrow : forall T1 T2 t, has_type empty t (Arrow T1 T2) ->
                      halts t ->
                      (forall s, R T1 s -> R T2 (app t s)) ->
                      R (Arrow T1 T2) t.

    Unfortunately, Coq rejects this definition because it violates the
    _strict positivity requirement_ for inductive definitions, which says
    that the type being defined must not occur to the left of an arrow in
    the type of a constructor argument. Here, it is the third argument to
    [R_arrow], namely [(forall s, R T1 s -> R TS (app t s))], and
    specifically the [R T1 s] part, that violates this rule.  (The
    outermost arrows separating the constructor arguments don't count when
    applying this rule; otherwise we could never have genuinely inductive
    properties at all!)  The reason for the rule is that types defined
    with non-positive recursion can be used to build non-terminating
    functions, which as we know would be a disaster for Coq's logical
    soundness. Even though the relation we want in this case might be
    perfectly innocent, Coq still rejects it because it fails the
    positivity test.

    Fortunately, it turns out that we _can_ define [R] using a
    [Fixpoint]: *)

Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
   | Bool  => True
   | Arrow T1 T2 => (forall s, R T1 s -> R T2 (app t s))

   (* ... edit the next line when dealing with products *)
   | Prod T1 T2 => False    (* FILL IN HERE *)
   end).

(** As immediate consequences of this definition, we have that every
    element of every set [R_T] halts in a value and is closed with type
    [t] :*)

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H1;  assumption.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H1; assumption.
Qed.

(** Now we proceed to show the main result, which is that every
    well-typed term of type [T] is an element of [R_T].  Together with
    [R_halts], that will show that every well-typed term halts in a
    value.  *)

(* ================================================================= *)
(** **  Membership in [R_T] Is Invariant Under Reduction *)

(** We start with a preliminary lemma that shows a kind of strong
    preservation property, namely that membership in [R_T] is _invariant_
    under reduction. We will need this property in both directions,
    i.e., both to show that a term in [R_T] stays in [R_T] when it takes a
    forward step, and to show that any term that ends up in [R_T] after a
    step must have been in [R_T] to begin with.

    First of all, an easy preliminary lemma. Note that in the forward
    direction the proof depends on the fact that our language is
    determinstic. This lemma might still be true for nondeterministic
    languages, but the proof would be harder! *)

Lemma step_preserves_halting : forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  inversion STM; subst.
   exfalso.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
   rewrite (step_deterministic _ _ _ ST H). exists t''. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.

(** Now the main lemma, which comes in two parts, one for each
    direction.  Each proceeds by induction on the structure of the type
    [T]. In fact, this is where we make fundamental use of the
    structure of types.

    One requirement for staying in [R_T] is to stay in type [T]. In the
    forward direction, we get this from ordinary type Preservation. *)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  (* Bool *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
  (* Arrow *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
  (* 请在此处解答 *) Admitted.

(** The generalization to multiple steps is trivial: *)

Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.

(** In the reverse direction, we must add the fact that [t] has type
   [T] before stepping as an additional hypothesis. *)

Lemma step_preserves_R' : forall T t t',
  has_type empty t T -> (t --> t') -> R T t' -> R T t.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma multistep_preserves_R' : forall T t t',
  has_type empty t T -> (t -->* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.

(* ================================================================= *)
(** ** Closed Instances of Terms of Type [t] Belong to [R_T] *)

(** Now we proceed to show that every term of type [T] belongs to
    [R_T].  Here, the induction will be on typing derivations (it would be
    surprising to see a proof about well-typed terms that did not
    somewhere involve induction on typing derivations!).  The only
    technical difficulty here is in dealing with the abstraction case.
    Since we are arguing by induction, the demonstration that a term
    [abs x T1 t2] belongs to [R_(T1->T2)] should involve applying the
    induction hypothesis to show that [t2] belongs to [R_(T2)].  But
    [R_(T2)] is defined to be a set of _closed_ terms, while [t2] may
    contain [x] free, so this does not make sense.

    This problem is resolved by using a standard trick to suitably
    generalize the induction hypothesis: instead of proving a statement
    involving a closed term, we generalize it to cover all closed
    _instances_ of an open term [t].  Informally, the statement of the
    lemma will look like this:

    If [x1:T1,..xn:Tn |- t : T] and [v1,...,vn] are values such that
    [R T1 v1], [R T2 v2], ..., [R Tn vn], then
    [R T ([x1:=v1][x2:=v2]...[xn:=vn]t)].

    The proof will proceed by induction on the typing derivation
    [x1:T1,..xn:Tn |- t : T]; the most interesting case will be the one
    for abstraction. *)

(* ----------------------------------------------------------------- *)
(** *** Multisubstitutions, Multi-Extensions, and Instantiations *)

(** However, before we can proceed to formalize the statement and
    proof of the lemma, we'll need to build some (rather tedious)
    machinery to deal with the fact that we are performing _multiple_
    substitutions on term [t] and _multiple_ extensions of the typing
    context.  In particular, we must be precise about the order in which
    the substitutions occur and how they act on each other.  Often these
    details are simply elided in informal paper proofs, but of course Coq
    won't let us do that. Since here we are substituting closed terms, we
    don't need to worry about how one substitution might affect the term
    put in place by another.  But we still do need to worry about the
    _order_ of substitutions, because it is quite possible for the same
    identifier to appear multiple times among the [x1,...xn] with
    different associated [vi] and [Ti].

    To make everything precise, we will assume that environments are
    extended from left to right, and multiple substitutions are performed
    from right to left.  To see that this is consistent, suppose we have
    an environment written as [...,y:bool,...,y:nat,...]  and a
    corresponding term substitution written as [...[y:=(tbool
    true)]...[y:=(const 3)]...t].  Since environments are extended from
    left to right, the binding [y:nat] hides the binding [y:bool]; since
    substitutions are performed right to left, we do the substitution
    [y:=(const 3)] first, so that the substitution [y:=(tbool true)] has
    no effect. Substitution thus correctly preserves the type of the term.

    With these points in mind, the following definitions should make sense.

    A _multisubstitution_ is the result of applying a list of
    substitutions, which we call an _environment_. *)

Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) {struct ss} : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' ([x:=s]t)
end.

(** We need similar machinery to talk about repeated extension of a
    typing context using a list of (identifier, type) pairs, which we
    call a _type assignment_. *)

Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.

(** We will need some simple operations that work uniformly on
    environments and type assigments *)

Fixpoint lookup {X:Set} (k : string) (l : list (string * X)) {struct l}
              : option X :=
  match l with
    | nil => None
    | (j,x) :: l' =>
      if eqb_string j k then Some x else lookup k l'
  end.

Fixpoint drop {X:Set} (n:string) (nxs:list (string * X)) {struct nxs}
            : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if eqb_string n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.

(** An _instantiation_ combines a type assignment and a value
    environment with the same domains, where corresponding elements are
    in R. *)

Inductive instantiation :  tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v c e,
    value v -> R T v ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,v)::e).

(** We now proceed to prove various properties of these definitions. *)

(* ----------------------------------------------------------------- *)
(** *** More Substitution Facts *)

(** First we need some additional lemmas on (ordinary) substitution. *)

Lemma vacuous_substitution : forall  t x,
     ~ appears_free_in x t  ->
     forall t', [x:=t']t = t.
Proof with eauto.
  (* 请在此处解答 *) Admitted.

Lemma subst_closed: forall t,
     closed t  ->
     forall x t', [x:=t']t = t.
Proof.
  intros. apply vacuous_substitution. apply H.  Qed.

Lemma subst_not_afi : forall t x v,
    closed v ->  ~ appears_free_in x ([x:=v]t).
Proof with eauto.  (* rather slow this way *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
    - (* var *)
     destruct (eqb_stringP x s)...
     inversion A; subst. auto.
    - (* app *)
     inversion A; subst...
    - (* abs *)
     destruct (eqb_stringP x s)...
     + inversion A; subst...
     + inversion A; subst...
    - (* pair *)
     inversion A; subst...
    - (* fst *)
     inversion A; subst...
    - (* snd *)
     inversion A; subst...
    - (* tru *)
     inversion A.
    - (* fls *)
     inversion A.
    - (* test *)
     inversion A; subst...
Qed.

Lemma duplicate_subst : forall t' x t v,
  closed v -> [x:=t]([x:=v]t') = [x:=v]t'.
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi.  auto.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    [x1:=v1]([x:=v]t) = [x:=v]([x1:=v1]t).
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_stringP x s); destruct (eqb_stringP x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite <- eqb_string_refl. apply subst_closed...
   + subst. simpl. rewrite <- eqb_string_refl. rewrite subst_closed...
   + simpl. rewrite false_eqb_string... rewrite false_eqb_string...
  (* 请在此处解答 *) Admitted.

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Substitutions *)

Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.

(** Closed environments are those that contain only closed terms. *)

Fixpoint closed_env (env:env) {struct env} :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

(** Next come a series of lemmas charcterizing how [msubst] of closed terms
    distributes over [subst] and over each term form *)

Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
    msubst env ([x:=v]t) = [x:=v](msubst (drop x env) t).
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0. fold closed_env in H2.
  destruct (eqb_stringP s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.

Lemma msubst_var:  forall ss x, closed_env ss ->
   msubst ss (var x) =
   match lookup x ss with
   | Some t => t
   | None => var x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
     simpl. destruct (eqb_string s x).
      apply msubst_closed. inversion H; auto.
      apply IHss. inversion H; auto.
Qed.

Lemma msubst_abs: forall ss x T t,
  msubst ss (abs x T t) = abs x T (msubst (drop x ss) t).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (eqb_string s x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2, msubst ss (app t1 t2) = app (msubst ss t1) (msubst ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.

(** You'll need similar functions for the other term constructors. *)

(* 请在此处解答 *)

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Extensions *)

(** We need to connect the behavior of type assignments with that of
    their corresponding contexts. *)

Lemma mupdate_lookup : forall (c : tass) (x:string),
    lookup x c = (mupdate empty c) x.
Proof.
  induction c; intros.
    auto.
    destruct a. unfold lookup, mupdate, update, t_update. destruct (eqb_string s x); auto.
Qed.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
    = if eqb_string x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  induction c; intros.
  - destruct (eqb_stringP x x'); auto.
  - destruct a. simpl.
    destruct (eqb_stringP s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_stringP x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_stringP s x'); auto.
      subst. rewrite false_eqb_string; congruence.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of Instantiations *)

(** These are strightforward. *)

Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
    solve_by_invert.
    simpl in *.
    destruct (eqb_string x x0); eauto.
Qed.

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split.  eapply typable_empty__closed. eapply R_typable_empty. eauto.
        auto.
Qed.

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve_by_invert.
    unfold lookup in *.  destruct (eqb_string x x').
      inversion G; inversion E; subst.  auto.
      eauto.
Qed.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop. destruct (eqb_string x x0); auto. constructor; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Congruence Lemmas on Multistep *)

(** We'll need just a few of these; add them as the demand arises. *)

Lemma multistep_App2 : forall v t t',
  value v -> (t -->* t') -> (app v t) -->* (app v t').
Proof.
  intros v t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto.  auto.
Qed.

(* 请在此处解答 *)

(* ----------------------------------------------------------------- *)
(** *** The R Lemma. *)

(** We can finally put everything together.

    The key lemma about preservation of typing under substitution can
    be lifted to multi-substitutions: *)

Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, has_type (mupdate Gamma c) t S ->
     has_type Gamma (msubst e t) S.
Proof.
  induction 1; intros.
    simpl in H. simpl. auto.
    simpl in H2.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.

(** And at long last, the main lemma. *)

Lemma msubst_R : forall c env t T,
    has_type (mupdate empty c) t T ->
    instantiation c env ->
    R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var.  rewrite P. auto. eapply instantiation_env_closed; eauto.

  - (* T_Abs *)
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT: has_type empty (abs x T11 (msubst (drop x env0) t12)) (Arrow T11 T12)).
    { eapply T_Abs. eapply msubst_preserves_typing.
      { eapply instantiation_drop; eauto. }
      eapply context_invariance.
      { apply HT. }
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_stringP x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl.  rewrite false_eqb_string; auto.
        simpl. destruct a.  unfold update, t_update.
        destruct (eqb_string s x0); auto. }
    unfold R. fold R. split.
       auto.
     split. apply value_halts. apply v_abs.
     intros.
     destruct (R_halts H0) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H0).
     apply multistep_preserves_R' with (msubst ((x,v)::env0) t12).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply multi_trans.  eapply multistep_App2; eauto.
       eapply multi_R.
       simpl.  rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T11)::c)).
          intros. unfold update, t_update, lookup. destruct (eqb_string x x0); auto.
       constructor; auto.

  - (* T_App *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2.  fold R in P1.  auto.

  (* 请在此处解答 *) Admitted.

(* ----------------------------------------------------------------- *)
(** *** Normalization Theorem *)

(** And the final theorem: *)

Theorem normalization : forall t T, has_type empty t T -> halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.


(* Fri Jul 19 00:33:16 UTC 2019 *)
