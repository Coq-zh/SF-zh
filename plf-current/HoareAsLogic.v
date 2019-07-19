(** * HoareAsLogic: 证明论霍尔逻辑  *)

(** 在[Hoare]一章中所介绍的霍尔逻辑可以被认为是“模型论”的：每一个构造子
    的证明规则以关于求值行为的_'定理'_的形式呈现，并且程序正确性（霍尔三元组的有
    效性）的证明由在Coq里面直接组合这些定理所构造。

    另外一种介绍霍尔逻辑的方式是定义一个完全分开的证明系统——关于命令，霍尔三元组
    等等的一系列公理和推断规则——接着说明霍尔三元组的一个证明是在_'那个'_逻辑中的一
    个合法导出式。这可以通过给出在这个新逻辑中的_'合法导出式'_的归纳定义来实现。

    这一章是可选的。在阅读之前，你会想要阅读一下在_'逻辑基础'_（_'软件基础'_的
    第一卷）中的 [ProofObjects] 章节。 *)

From PLF Require Import Imp.
From PLF Require Import Hoare.

(* ################################################################# *)
(** * 定义 *)

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      hoare_proof P (SKIP) P
  | H_Asgn : forall Q V a,
      hoare_proof (assn_sub V a Q) (V ::= a) Q
  | H_Seq  : forall P c Q d R,
      hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
  | H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (TEST b THEN c1 ELSE c2 FI) Q
  | H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

(** 我们并不需要包含对应 [hoare_consequence_pre] 或 [hoare_consequence_post] 的公理，
    因为它们可以简单地通过 [H_Consequence] 被证明。 *)

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X.  apply H.  intros. apply H0. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X. intros. apply H0.  apply H. Qed.

(** 作为一个例子，让我们构造一个证明对象，来表示这个霍尔三元组的一个导出式

      {{(X=3) [X |-> X + 2] [X |-> X + 1]}}
      X::=X+1 ;; X::=X+2
      {{X=3}}.

    我们可以让 Coq 的策略来帮助我们构造这个证明对象。 *)

Example sample_proof :
  hoare_proof
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    (X ::= X + 1;; X ::= X + 2)
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq; apply H_Asgn.
Qed.

(*
Print sample_proof.

====>
  H_Seq
  (((fun st : state => st X = 3) [X |-> X + 2]) [X |-> X + 1])
  (X ::= X + 1)
  ((fun st : state => st X = 3) [X |-> X + 2])
  (X ::= X + 2)
  (fun st : state => st X = 3)
  (H_Asgn
     ((fun st : state => st X = 3) [X |-> X + 2])
     X (X + 1))
  (H_Asgn
     (fun st : state => st X = 3)
     X (X + 2))
*)

(* ################################################################# *)
(** * 性质 *)

(** **** 练习：2 星, standard (hoare_proof_sound)  

    证明这些证明对象是正确的断言。 *)

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 我们也可以使用Coq的推理工具来证明关于霍尔逻辑的元定理。例如，下述是我们在
    [Hoare] 章节中看到的两条定理的模拟——这一次，使用霍尔逻辑导出式（可证明
    性），而不是直接使用霍尔三元组的语义，来表达这些定理。

    第一条定理表达，对于所有的 [P] 和 [c]，断言 [{{P}} c {{True}}] 在霍尔逻辑中是
    _'可证明的'_。注意到这个证明比在[Hoare]中的语义证明更加复杂：实际上我们需要在命令
    [c] 的结构上应用归纳法 。 *)

Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  induction c; intro P.
  - (* SKIP *)
    eapply H_Consequence.
    apply H_Skip.
    intros. apply H.
    (* Proof of True *)
    intros. apply I.
  - (* ::= *)
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  - (* ;; *)
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ => True)).
    apply IHc2.
    intros. apply I.
  - (* TEST *)
    apply H_Consequence_pre with (fun _ => True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  - (* WHILE *)
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

(** 类似地，我们可以说明对于任意的 [c] 和 [Q]，[{{False}} c {{Q}}] 是可证明的。 *)

Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  intros P Q [CONTRA HP].
  destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  induction c; intro Q.
  - (* SKIP *) pre_false_helper H_Skip.
  - (* ::= *) pre_false_helper H_Asgn.
  - (* ;; *) pre_false_helper H_Seq. apply IHc1. apply IHc2.
  - (* TEST *)
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  - (* WHILE *)
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.

(** 最后，我们可以说明 [hoare_proof] 公理集合足够用来证明关于任何（部分）正确性的
    事实。更准确地说，任何我们能够证明的语义霍尔三元组，都能够通过这些公理证明。
    这样的公理集合被称为_'相对完备的（relatively complete）'_。我们的证明的灵感来自
    于：

      https://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html

    为了完成这个证明，我们需要使用一种被称为
    _'最弱前置条件（weakest preconditions）'_的技术装置来创造一些中间的断言。

    给定一个命令[c]和一个想要的后置条件断言 [Q] ，最弱前置条件 [wp c Q] 是一个断言
    [P]，使得 [{{P}} c {{Q}}] 成立，并且对于任意其他断言 [P']，如果 [{{P}} c {{Q}}] 成立，那么
    [P' -> P]。我们可以更加直接地将其定义为： *)

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

(** **** 练习：1 星, standard (wp_is_precondition)  *)

Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (wp_is_weakest)  *)

Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
(* 请在此处解答 *) Admitted.

(** 下面这个辅助引理也很有用。 *)

Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.
(** [] *)

(** **** 练习：5 星, standard (hoare_proof_complete)  

    完成如下定理的证明。 *)

Theorem hoare_proof_complete: forall P c Q,
  {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply H_Consequence.
     eapply H_Skip.
      intros.  eassumption.
      intro st. apply HT.  apply E_Skip.
  - (* ::= *)
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  - (* ;; *)
    apply H_Seq with (wp c2 Q).
     eapply IHc1.
       intros st st' E1 H. unfold wp. intros st'' E2.
         eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E1 H. apply H; assumption.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 最后，我们可能希望我们的公理霍尔逻辑是_'可决定的（decidable）'_；也就是说，这里
    有一个（会终止的）算法（一个_'决定性过程（decision procedure）'_）来决定一个给
    定的霍尔三元组是否是合法的（可导出的）。但是这样的一个决定性过程并不存在！

    考虑三元组 [{{True}} c {{False}}]。这个三元组是有效的当且仅当 [c] 不终止。这意味着，
    任何一个能够决定任意三元组的合法性的算法能够解决停机问题（Halting Problem）。

    类似地，三元组 [{{True}} SKIP {{P}}] 是合法的当且仅当 [forall s, P s] 是合法的，其中 [P]
    是Coq逻辑的任意一个断言。但是我们已知对于这个逻辑并没有任何的决定性过程。

    总而言之，此公理化表述更清晰地诠释如何“出具霍尔逻辑下的证明”。
    但是，从实际上我们需要写出这些证明的角度来看，这并不让人完全
    满意：这太冗长了。在 [Hoare2] 一章中的关于形式化修饰程序的章节会向我们展
    示如何做的更好。 *)

(* Fri Jul 19 00:33:14 UTC 2019 *)
