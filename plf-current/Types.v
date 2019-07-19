(** * Types: 类型系统 *)

(** 我们接下来主要的话题是_'类型系统'_——一种根据表达式结果的“形状（shapes）”
    来给表达式分类的静态程序分析技术。我们将会以一个最简单的有类型语言为起点，介绍
    类型和定型规则的概念，以及类型系统最基础的几个定理：_'保型性（type preservation）'_
    和_'可进性（progress）'_。在 [Stlc] 一章中，我们会继续考察
    _'简单类型λ-演算'_，它是几乎每个现代函数式语言的核心（也包括 Coq！）。 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.

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

    t ::= tru
        | fls
        | test t then t else t
        | zro
        | scc t
        | prd t
        | iszro t

    以及形式化的： *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

(** 对_'值（values）'_的定义包括 [tru]，[fls] 以及数值…… *)

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

(* ================================================================= *)
(** ** 操作语义 *)

(** 首先我们非形式化地描述单步关系…… 

                   -------------------------------                  (ST_TestTru)
                   test tru then t1 else t2 --> t1

                   -------------------------------                  (ST_TestFls)
                   test fls then t1 else t2 --> t2

                               t1 --> t1'
            ----------------------------------------------------       (ST_Test)
            test t1 then t2 else t3 --> test t1' then t2 else t3

                             t1 --> t1'
                         ------------------                             (ST_Scc)
                         scc t1 --> scc t1'

                           ---------------                           (ST_PrdZro)
                           prd zro --> zro

                         numeric value v1
                        -------------------                          (ST_PrdScc)
                        prd (scc v1) --> v1

                              t1 --> t1'
                         ------------------                             (ST_Prd)
                         prd t1 --> prd t1'

                          -----------------                        (ST_IszroZro)
                          iszro zro --> tru

                         numeric value v1
                      ----------------------                       (ST_IszroScc)
                      iszro (scc v1) --> fls

                            t1 --> t1'
                       ----------------------                         (ST_Iszro)
                       iszro t1 --> iszro t1'
*)

(** 接着形式化地： *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall t1,
      nvalue t1 ->
      (prd (scc t1)) --> t1
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall t1,
       nvalue t1 ->
      (iszro (scc t1)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(** 请注意 [step] 关系并不在意步进表达式是否有全局意义——它只是检查_'下一步'_
    的归约操作是否在正确的操作对象上。比如，项 [succ true]
    无法前进一步，但这个几乎显然无意义的项

       scc (test tru then tru else tru)

    却可以前进一步（注意是在卡住之前）。 *)

(* ================================================================= *)
(** ** 正规式和值 *)

(** 首先值得注意的是 [Smallstep] 一章中的强可进性定理对这里的 [step]
    归约并不成立。也即，有一些项是正规式（他们无法再前进一步），但却不是值（因为
    我们还没有把他们包括进潜在“归约结果”的定义中）。这样的项_'卡住了'_。 *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** 练习：2 星, standard (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 然而，值和正规式在这个语言中_'并不'_相同，值的集合被包括在正规式的集合中。
    这一点很重要，因为这说明我们没有不小心定义了一些仍然能前进一步的值。*)

(** **** 练习：3 星, standard (value_is_nf)  *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* 请在此处解答 *) Admitted.

(** （提示：在证明中的某个地方，你需要使用归纳来推理某个项，这个项已知是数值。
    归纳可以对项本身进行，也可以对它是数值这个证据进行。两种方法均可完成证明，
    但你发现一种要比另一种稍微简短一点。作为练习，请尝试使用这两种方法完成证明。）

    [] *)

(** **** 练习：3 星, standard, optional (step_deterministic)  

    使用 [value_is_nf] 来证明 [step] 关系是确定的。*)

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
  | Bool : ty
  | Nat : ty.

(** 在非形式化的记号中，类型关系经常写做 [|- t \in T]，并读做“[t] 有类型 [T]”。
    [|-] 符号叫做“十字转门（turnstile）”。下面，我们会看到更加丰富的类型关系，其中
    我们会在 [|-] 左侧添加一个或多个“上下文（context）”。目前暂时来说，上下文总是空的。 

    
                           ---------------                     (T_Tru)
                           |- tru \in Bool

                          ---------------                      (T_Fls)
                          |- fls \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------     (T_Test)
                    |- test t1 then t2 else t3 \in T

                             --------------                    (T_Zro)
                             |- zro \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Scc)
                          |- scc t1 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Prd)
                          |- prd t1 \in Nat

                            |- t1 \in Nat
                        --------------------                 (T_IsZro)
                        |- iszro t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
    - apply T_Fls.
    - apply T_Zro.
    - apply T_Scc.
       + apply T_Zro.
Qed.

(** （因为我们在提示数据库（hint database）中包括了类型关系的所有构造子，
    因此 [auto] 策略可以自动完成这个证明。）*)

(** 重要的一点是认识到类型关系是一个_'保守的（conservative）'_
    （或_'静态的（static）'_）近似：它不考虑项被归约时会发生什么——特别地，
    它并不计算项的正规式的类型。 *)

Example has_type_not :
  ~ ( |- test fls zro tru \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** 练习：1 星, standard, optional (scc_hastype_nat__hastype_nat)  *)
Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 典范形式 *)

(** 下面的两个引理作为基础性质表达了布尔值和数值的定义同类型关系相一致。*)

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** 可进性 *)

(** 类型关系具有两个十分重要的性质。第一个是良型（well-typed）的正规式不会卡住——或者，反过来说，
    如果一个项是良型的，那么它要么是一个值，要么可以至少前进一步。我们把这个性质叫做
    _'可进性（progress）'_。 *)

(** **** 练习：3 星, standard (finish_progress)  *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

(** 请完成 [progress] 性质的形式化证明。（在开始前请确保你理解了下一个练习中的非
    形式化证明——这会节省很多你的时间。）*)
Proof with auto.
  intros t T HT.
  induction HT...
  (* 对于显然是值的情形，比如 T_Tru 和 T_Fls，我们直接使用 auto 完成。*)
  - (* T_Test *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 是值 *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 可前进一步 *)
      inversion H as [t1' H1].
      exists (test t1' t2 t3)...
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (finish_progress_informal)  

    请完成非形式化的证明： *)

(** _'定理'_：如果 [|- t \in T]，那么 [t] 要么是值，要么存在某个 [t'] 使 [t --> t']。*)

(** _'证明'_：对 [|- t \in T] 的导出式进行归纳。

      - 如果导出式的最后一条规则是 [T_Test]，那么 [t = test t1 then t2 else t3]，
        其中 [|- t1 \in Bool]，[|- t2 \in T] 以及 [|- t3 \in T]。
        根据归纳假设，[t1] 要么是值，要么可前进一步到某个 [t1']。

      - 如果 [t1] 是值，那么根据典范形式（canonical forms）引理以及
        [|- t1 \in Bool] 的事实，可得 [t1] 是一个 [bvalue]——也即，
        它要么是 [tru] 要么是 [fls]。如果 [t1 = tru]，由 [ST_TestTru]
        可得 [t] 前进到 [t2]；而当 [t1 = fls] 时，由 [ST_TestFls]
        可得 [t] 前进到 [t3]。不论哪种情况，[t] 都可以前进一步，这是我们
        想要证明的。

      - 如果 [t1] 自己可以前进一步，那么根据 [ST_Test] 可得 [t] 也可以。

    - (* 请在此处解答 *)
 *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(** 这个定理要比 [Smallstep] 一章中的强可进性定理更有趣一些，在强可进性定理
    中_'全部'_的正规式都是值。这里项可以卡住，但仅当它为劣型时。 *)

(* ================================================================= *)
(** ** 保型性 *)

(** 关于类型的第二个重要性质是，当一个良型项可前进一步时，其结果也是一个良型项。*)

(** **** 练习：2 星, standard (finish_preservation)  *)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
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
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (finish_preservation_informal)  

    请完成非形式化的证明： *)

(** _'定理'_：如果 [|- t \in T] 且 [t --> t']，那么 [|- t' \in T]。 *)

(** _'证明'_：对 [|- t \in T] 的导出式进行归纳。

      - 如果导出式的最后一条规则是 [T_Test]，那么 [t = test t1
        then t2 else t3]，其中 [|- t1 \in Bool]， [|- t2 \in T] 以及 [|- t3
        \in T]。

        请记着 [t] 形如 [test ...]，通过检查小步归约关系的规则，我们看到可以用来证明
        [t --> t'] 的规则仅有 [ST_TestTru]，[ST_TestFls] 或者 [ST_Test]。

      - 如果最后的规则是 [ST_TestTru]，那么 [t' = t2]。但是我们有
        [|- t2 \in T]，所以证明完成。

      - 如果最后的规则是 [ST_TestFls]，那么 [t' = t3]。但是我们有
        [|- t3 \in T]，所以证明完成。

      - 如果最后的规则是 [ST_Test]，那么 [t' = test t1' then t2
        else t3]，其中 [t1 --> t1']。我们知道 [|- t1 \in Bool]，
        因此根据归纳假设可得 [|- t1' \in Bool]。正如需要的那样，规则
        [T_Test] 为我们提供了 [|- test t1' then t2 else t3 \in T]。

    - (* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, standard (preservation_alternate_proof)  

    现在请对_'求值'_导出式（而非类型导出式）进行归纳来证明保型性定理。
    请仔细阅读和思考上面证明中最开始的几行，确保你理解了他们是在做什么。
    本证明的开始部分类似，但并不完全一样。*)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 保型性定理也经常被称作_'主语归约（subject reduction）'_，因为它告诉了
    我们当类型关系的主语被归约时会发生什么。这一属于来自于把类型陈述想象为一句话，
    其中项是主语，类型是谓语。 *)

(* ================================================================= *)
(** ** 类型可靠性 *)

(** 把可进行与保型性放在一起，我们可以看到一个良型的项永远不会有卡住状态。*)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* ================================================================= *)
(** ** 额外练习 *)

(** **** 练习：2 星, standard, recommended (subject_expansion)  

    在学习了主语归约属性后，你可能会好奇其相反的属性——主语_'扩张'_（subject expasion）
    ——是否也成立。也即，如果有 [t --> t'] 且 [|- t' \in T]，是否总是有
    [|- t \in T]？如果是的话，请证明它。如果不是的话，请给出一个反例。
    （你并不需要在 Coq 中证明你的反例，不过也可以这样做。）

    (* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_subject_expansion : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (variation1)  

    假设我们为类型关系添加新的规则：

      | T_SccBool : forall t,
           |- t \in Bool ->
           |- scc t \in Bool

  下面的哪些性质仍然成立？对于每个性质，写下“仍然成立”或“不成立”。
  如果性质不再成立，请给出一个反例。
      - [step] 的确定性
            (* 请在此处解答 *)
      - 可进性
            (* 请在此处解答 *)
      - 保型性
            (* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (variation2)  

    假设，我们仅为 [step] 关系添加新的规则：

      | ST_Funny1 : forall t2 t3,
           (test tru t2 t3) --> t3

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。
            (* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard, optional (variation3)  

    假设，我们仅添加新的规则：

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (test t1 t2 t3) --> (test t1 t2' t3)

   this rule?  For each one that does, give a counter-example.
            (* 请在此处解答 *)

    [] *)

(** **** 练习：2 星, standard, optional (variation4)  

    假设，我们仅添加新的规则：

      | ST_Funny3 :
          (prd fls) --> (prd (prd fls))

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。
(* 请在此处解答 *)

    [] *)

(** **** 练习：2 星, standard, optional (variation5)  

    假设，我们仅添加新的规则：

      | T_Funny4 :
            |- zro \in Bool

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。
(* 请在此处解答 *)

    [] *)

(** **** 练习：2 星, standard, optional (variation6)  

    假设，我们仅添加新的规则：

      | T_Funny5 :
            |- prd zro \in Bool

   上面的哪些性质不再成立？对于不再成立的性质，给出一个反例。
(* 请在此处解答 *)

    [] *)

(** **** 练习：3 星, standard, optional (more_variations)  

    请使用上面的模式编写更多的练习。尝试有选择地使某些性质不再成立——
    即，对定义的改变只会导致某一个性质不再成立，而其他仍然成立。
*)
(* 请在此处解答 

    [] *)

(** **** 练习：1 星, standard (remove_prdzro)  

    归约规则 [ST_PrdZro] 可能有一点反直觉：我们想要让 [ zro] 的前趋变为未定义的，
    而非定义为 [zro]。我们是否可以通过仅仅移除 [step] 中的某条规则达到这一点？
    这样做会导致别的问题出现吗？

(* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_remove_predzro : option (nat*string) := None.
(** [] *)

(** **** 练习：4 星, advanced (prog_pres_bigstep)  

    假设我们的求值关系是以大步语义方式定义的。请陈述类似的可进性和保型性定理。
    （你不需要证明他们。）

    你可以发现这两个属性中存在的局限吗？他们是否允许非停机的命令？我们为什么倾向于
    使用小步语义来陈述保型性和可进性？

(* 请在此处解答 *)
*)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)



(* Fri Jul 19 00:33:15 UTC 2019 *)
