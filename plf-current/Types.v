(** * Types: 类型系统 *)

(** 我们接下来主要的话题是_'类型系统'_——一种根据表达式结果的“形状（shapes）”
    来给表达式分类的静态程序分析技术。我们将会以一个最简单的有类型语言为起点，介绍
    类型和定型规则的概念，以及类型系统最基础的几个定理：_'维型性（type preservation）'_
    和_'可进性（progress）'_。在 [Stlc] 一章中，我们会继续考察
    _'简单类型λ-演算'_，它是几乎每个现代函数式语言的核心（也包括 Coq！）。 *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

(* ################################################################# *)
(** * 有类型算数表达式 *)

(** 作为对类型系统讨论的动机，让我们像过去一样以一个小型玩具语言开始。
    我们想要让程序有机会产生运行时类型错误，因此除了 [Smallstep] 
    一章中用到的常量和加法，还需要一点更复杂的语言构造：只有一种数据类型（比如说数字）
    太过于简单，但是两种（数字和布尔值）便足够产生有趣的故事了。

    语言的定义部分没有什么特别值得注意的。 *)

(* ================================================================= *)
(** ** 语法 *)

(** 这是非形式化的语法表述：

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t

    以及形式化的： *)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(** 对_'值（values）'_的定义包括 [true]，[false] 以及数值…… *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

(* ================================================================= *)
(** ** 操作语义 *)

(** 首先我们非形式化地描述单步关系…… *)
(**

                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
            ------------------------------------------------            (ST_If)
            if t1 then t2 else t3 ==> if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'
*)

(** 接着形式化地： *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(** 请注意 [step] 关系并不在意表达式是否有全局意义——它只是检查_'下一步'_
    的归约操作是否在正确的操作对象上。比如，项 [succ true]（用形式语法来说是 
    [tsucc true]）无法前进一步，但这个几乎显然无意义的项

       succ (if true then true else true)

    却可以前进一步（注意是在卡住之前）。 *)

(* ================================================================= *)
(** ** 正规式和值 *)

(** 首先值得注意的是 [Smallstep] 一章中的强可进性定理对这里的 [step]
    归约并不成立。也即，有一些项是正规式（他们无法再前进一步），但却不是值（因为
    我们还没有把他们包括进潜在“归约结果”的定义中）。这样的项_'卡住了'_。 *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** 练习：2 星 (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 然而，值和正规式在这个语言中并_'不'_相同，值的集合被包括在正规式的集合中。
    这一点很重要，因为这说明我们没有不小心定义了一些仍然能前进一步的值。*)

(** **** 练习：3 星 (value_is_nf)  *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* 请在此处解答 *) Admitted.

(** （提示：在证明中的某个地方，你需要使用归纳来推理某个项，这个项已知是数值。
    归纳可以对项本身进行，也可以对它是数值这个证据进行。两种方法均可完成证明，
    但你发现一种要比另一种稍微简短一点。作为练习，请尝试使用这两种方法完成证明。）*)
(** [] *)

(** **** 练习：3 星, optional (step_deterministic)  *)
(** 使用 [value_is_nf] 来证明 [step] 关系是确定的。*)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 定型 *)

(** 下一个重要的观察是，尽管这个语言中有卡住的项，他们总是以混合了
    布尔值和数字的方式变得完全没有意义，我们也_'不想'_为他们赋予意义。
    通过定义_'类型关系（typing relation）'_关联起项和他们最终结果的
    类型（数字或布尔值），我们可以容易地排除这些劣型（ill-typed）项。*)

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

(** 在非形式化的记号中，类型关系经常写做 [|- t \in T]，并读做“[t] 有类型 [T]”。
    [|-] 符号叫做“十字转门（turnstile）”。下面，我们会看到更加丰富的类型关系，其中
    我们会在 [|-] 左侧添加一个或多个“上下文（context）”。目前暂时来说，上下文总是空的。 *)
(** 
                           ----------------                            (T_True)
                           |- true \in Bool

                          -----------------                           (T_False)
                          |- false \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------                (T_If)
                    |- if t1 then t2 else t3 \in T

                             ------------                              (T_Zero)
                             |- 0 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Succ)
                          |- succ t1 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Pred)
                          |- pred t1 \in Nat

                            |- t1 \in Nat
                        ---------------------                        (T_IsZero)
                        |- iszero t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- ttrue \in TBool
  | T_False :
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero :
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof.
  apply T_If.
    - apply T_False.
    - apply T_Zero.
    - apply T_Succ.
       + apply T_Zero.
Qed.

(** （因为我们在提示数据库（hint database）中包括了类型关系的所有构造子，
    因此 [auto] 策略可以自动完成这个证明。）*)

(** 重要的一点是认识到类型关系是一个_'保守的（conservative）'_
    （或_'静态的（static）'_）近似：它不考虑项被归约时会发生什么——特别地，
    它并不计算项的正规式的类型。 *)

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** 练习：1 星, optional (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 典范形式 *)

(** 下面的两个引理作为基础性质表达了布尔值和数值的定义同类型关系相一致。*)

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.
  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.
  auto.
Qed.

(* ================================================================= *)
(** ** 可进性 *)

(** 类型关系具有两个十分重要的性质。第一个是良型（well-typed）的正规式不会卡住——或者，反过来说，
    如果一个项是良型的，那么它要么是一个值，要么可以至少前进一步。我们把这个性质叫做
    _'可进性（progress）'_。 *)

(** **** 练习：3 星 (finish_progress)  *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

(** 请完成 [progress] 性质的形式化证明。（在开始前请确保你理解了下一个练习中的非
    形式化证明——这会节省很多你的时间。）*)
Proof with auto.
  intros t T HT.
  induction HT...
  (* 对于显然是值的情形，比如 T_True 和 T_False，我们直接使用 auto 完成。*)
  - (* T_If *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 是值 *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 可前进一步 *)
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (finish_progress_informal)  *)
(** 请完成非形式化的证明： *)

(** _'定理'_：如果 [|- t \in T]，那么 [t] 要么是值，要么存在某个 [t'] 使 [t ==> t']。*)

(** _'证明'_：对 [|- t \in T] 的导出式进行归纳。

      - 如果导出式的最后一条规则是 [T_If]，那么 [t = if t1 then t2 else t3]，
        其中 [|- t1 \in Bool]，[|- t2 \in T] 以及 [|- t3 \in T]。
        根据归纳假设，[t1] 要么是值，要么可前进一步到某个 [t1']。

            - 如果 [t1] 是值，那么根据典范形式（canonical forms）引理以及
              [|- t1 \in Bool] 的事实，可得 [t1] 是一个 [bvalue]——也即，
              它要么是 [true] 要么是 [false]。如果 [t1 = true]，由 [ST_IfTrue]
              可得 [t] 前进到 [t2]；而当 [t1 = false] 时，由 [ST_IfFalse]
              可得 [t] 前进到 [t3]。不论哪种情况，[t] 都可以前进一步，这是我们
              想要证明的。

            - 如果 [t1] 自己可以前进一步，那么根据 [ST_If] 可得 [t] 也可以。

      - (* 请在此处解答 *)
 *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_finish_progress_informal : option (prod nat string) := None.
(** [] *)

(** 这个定理要比 [Smallstep] 一章中的强可进性定理更有趣一些，在强可进性定理
    中_'全部'_的正规式都是值。这里项可以卡住，但仅当它为劣型时。 *)

(* ================================================================= *)
(** ** 维型性 *)

(** 关于类型的第二个重要性质是，当一个良型项可前进一步时，其结果也是一个良型项。*)

(** **** 练习：2 星 (finish_preservation)  *)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(** 请完成 [preservation] 性质的形式化证明。（和上次一样，在开始前请确保你理解了
    下一个练习中的非形式化证明。） *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* 每个情形都需要引入一些东西 *)
         intros t' HE;
         (* 我们还需要处理一些不可能发生的情形 *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (finish_preservation_informal)  *)
(** 请完成非形式化的证明： *)

(** _'定理'_：如果 [|- t \in T] 且 [t ==> t']，那么 [|- t' \in T]。 *)

(** _'证明'_：对 [|- t \in T] 的导出式进行归纳。

      - 如果导出式的最后一条规则是 [T_If]，那么 [t = if t1
        then t2 else t3]，其中 [|- t1 \in Bool]， [|- t2 \in T] 以及 [|- t3
        \in T]。

        请记着 [t] 形如 [if ...]，通过检查小步归约关系的规则，我们看到可以用来证明
        [t ==> t'] 的规则仅有 [ST_IfTrue]，[ST_IfFalse] 或者 [ST_If]。

           - 如果最后的规则是 [ST_IfTrue]，那么 [t' = t2]。但是我们有
             [|- t2 \in T]，所以证明完成。

           - 如果最后的规则是 [ST_IfFalse]，那么 [t' = t3]。但是我们有
             [|- t3 \in T]，所以证明完成。

           - 如果最后的规则是 [ST_If]，那么 [t' = if t1' then t2
             else t3]，其中 [t1 ==> t1']。我们知道 [|- t1 \in Bool]，
             因此根据归纳假设可得 [|- t1' \in Bool]。正如需要的那样，规则
             [T_If] 为我们提供了 [|- if t1' then t2 else t3 \in T]。

      - (* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_finish_preservation_informal : option (prod nat string) := None.
(** [] *)

(** **** 练习：3 星 (preservation_alternate_proof)  *)
(** 现在请对_'求值'_导出式（而非类型导出式）进行归纳来证明维型性定理。
    请仔细阅读和思考上面证明中最开始的几行，确保你理解了他们是在做什么。
    本证明的开始部分类似，但并不完全一样。*)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 维型性定理也经常被称作_'主语归约（subject reduction）'_，因为它告诉了
    我们当类型关系的主语被归约时会发生什么。这一属于来自于把类型陈述想象为一句话，
    其中项是主语，类型是谓语。 *)

(* ================================================================= *)
(** ** 类型可靠性 *)

(** 把可进行与维型性放在一起，我们可以看到一个良型的项永远不会有卡住状态。*)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* ################################################################# *)
(** * 题外话：[normalize] 策略 *)

(** 
    在使用 Coq 对程序语言的定义进行一些实验时，我们经常想要看看某个具体的项会归约到什么——
    也即，我们想要为形如 [t ==>* t'] 的目标找到证明，其中 [t] 是一个具体的项，而
    [t'] 是未知的。比如说，使用小步关系 [astep] 来归约一个算数表达式。*)

Module NormalizePlayground.
Import Smallstep.

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

(** 证明重复地应用了 [multi_step]，直到项被化简为一个正规式。幸运地是，如果有合适的
    提示，中间证明步骤可以被 [auto] 策略解决。*)

Hint Constructors step value.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(** 下面使用 [Tactic Notation] 自定义的策略捕捉了这种模式。此外，在每次归约前，
    我们打印出当前的目标，这样我们可以观察到项是如何被归约的。 *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  normalize.
  (* [normalize] 策略中的 [print_goal] 显示了项是如何一步步被归约的……
         (P (C 3) (P (C 3) (C 4)) ==>* C 10)
         (P (C 3) (C 7) ==>* C 10)
         (C 10 ==>* C 10)
  *)
Qed.

(** [normalize] 策略以一个目标和存在变量开始，提供了一种简单的方法计算出项的正规式。*)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  ==>* e'.
Proof.
  eapply ex_intro. normalize.
(* This time, the trace is:
       (P (C 3) (P (C 3) (C 4)) ==>* ?e')
       (P (C 3) (C 7) ==>* ?e')
       (C 10 ==>* ?e')
   这列的 ?e' 是由 eapply “猜”出来的变量。 *)
Qed.


(** **** 练习：1 星 (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  ==>* e'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, optional (normalize_ex')  *)
(** 作为比较，请使用 [apply] 而非 [eapply] 证明它。*)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  ==>* e'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

End NormalizePlayground.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

(* ================================================================= *)
(** ** 额外练习 *)

(** **** 练习：2 星, recommended (subject_expansion)  *)
(** 在学习了主语归约属性后，你可能会好奇其相反的属性——主语_'扩张'_（subject expasion）
    ——是否也成立。也即，如果有 [t ==> t'] 且 [|- t' \in T]，是否总是有
    [|- t \in T]？如果是的话，请证明它。如果不是的话，请给出一个反例。
    （你并不需要在 Coq 中证明你的反例，不过也可以这样做。）

    (* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_subject_expansion : option (prod nat string) := None.
(** [] *)

(** **** 练习：2 星 (variation1)  *)
(** 假设，我们为类型关系添加新的规则：

      | T_SuccBool : forall t,
           |- t \in TBool ->
           |- tsucc t \in TBool

  下面的哪些性质仍然成立？对于每个性质，写下“仍然成立”或“不成立”。
  如果性质不再成立，请给出一个反例。
      - [step] 的确定性

      - 可进性

      - 维型性

*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_variation1 : option (prod nat string) := None.
(** [] *)

(** **** 练习：2 星 (variation2)  *)
(** 假设，我们仅为 [step] 关系添加新的规则：

      | ST_Funny1 : forall t2 t3,
           (tif ttrue t2 t3) ==> t3

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。

*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_variation2 : option (prod nat string) := None.
(** [] *)

(** **** 练习：2 星, optional (variation3)  *)
(** 假设，我们仅添加新的规则：

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。


    [] *)

(** **** 练习：2 星, optional (variation4)  *)
(** 假设，我们仅添加新的规则：

      | ST_Funny3 :
          (tpred tfalse) ==> (tpred (tpred tfalse))

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。


    [] *)

(** **** 练习：2 星, optional (variation5)  *)
(** 假设，我们仅添加新的规则：

      | T_Funny4 :
            |- tzero \in TBool

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。


    [] *)

(** **** 练习：2 星, optional (variation6)  *)
(** 假设，我们仅添加新的规则：

      | T_Funny5 :
            |- tpred tzero \in TBool

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。


    [] *)

(** **** 练习：3 星, optional (more_variations)  *)
(** 请使用上面的模式编写更多的练习。尝试有选择地使某些性质不再成立——
    即，对定义的改变只会导致某一个性质不再成立，而其他仍然成立。
*)
(** [] *)

(** **** 练习：1 星 (remove_predzero)  *)
(** 归约规则 [ST_PredZero] 可能有一点反直觉：我们想要让零的前继变为未定义的，
    而非定义为零。我们是否可以通过仅仅移除 [step] 中的某条规则达到这一点？
    这样做会导致别的问题出现吗？

(* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_remove_predzero : option (prod nat string) := None.
(** [] *)

(** **** 练习：4 星, advanced (prog_pres_bigstep)  *)
(** 假设我们的求值关系是以大步语义方式定义的。请陈述类似的可进性和维型性定理。
    （你不需要证明他们。）

    你可以发现这两个属性中存在的局限吗？他们是否允许非停机的命令？我们为什么倾向于
    使用小步语义来陈述维型性和可进性？

(* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_prog_pres_bigstep : option (prod nat string) := None.
(** [] *)

(** $Date$ *)
