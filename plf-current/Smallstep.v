(** * Smallstep: 小步操作语义 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

(** 我们目前见到的（对 [aexp]，[bexp] 和命令的）求值器是以“大步（big-step）”
    风格构造的：它们以“单一大步（one big-step）”的方式描述了一个表达式如
    何被求值到最终值上（或一个命令及存储被求值到最终存储上）。

    对许多目的而言，这种风格非常简单和自然——确实，它的普及者 Gilles Kahn 也把它
    叫做_'自然语义（natural semantics）'_。但仍然有一些它不擅长的事情。
    特别是，它并没有提供一种自然的方式来描述_'并发（concurrent）'_程序语言，
    其语义——即，程序如何运行的本质——不仅仅关于输入状态如何被映射到输出状态，
    还包括经过的中间状态，因为当代码并发执行时这些中间状态同样可以被观察到。

    大步语义风格的另一个缺点更加技术性，但在一些情况下却非常重要。假设我们定义了一个
    Imp 的变种，语言的变量是数字_'或'_数字的列表。这个扩展语言的语法允许我们写下例如
    [2 + nil] 这样的奇怪表达式，而算数表达式的语义则必须描述这样的表达式是如何执行的。
    一种方式是把列表也视作数字，并延续每个表达式都被求值到数字上的约定——比如，当上下文
    需要一个数字时，列表会被解释为 [0]。但这样做其实有一点敷衍了事。

    另一种更加自然的方式是说像 [2+nil] 这类表达式的行为是_'未定义的（undefined）'_
    ——即，它根本不会被求值到任何结果。我们可以简单地达到这个目的：只需要把 [aeval]
    和 [beval] 以 [Inductive] 命题而非 [Fixpoints] 的方式来编写，这样我们便可
    以表达偏函数而非全函数。

    然而，现在我们遇到了一个更严重地问题。在这个语言中，有_'两种非常不同的原因'_导致
    一个命令无法把初始状态映射到任何地结束状态：执行进入了无限循环；或者在某个点，程序
    尝试进行一个无意义的操作，比如对一个数字和列表求和，由此无法应用任何一个求值规则。

    这两种结果——非停机状态 vs. 在错误的结构上卡住（stuck）——不应当被混淆。特别地，我们想要
    以添加某种形式的_'类型检查（typechecking）'_的方式来_'允许'_第一种情况（这是我们为
    了方便地使用像 [while] 这类通用循环构造所付出的必要代价），但_'阻止'_第二种情况
    （也即错误的程序）。在剩下的课程中，这会是我们主要讨论的话题。作为第一步，我们需要一种
    语义来区分非停机状态和错误的“卡住状态（stuck states）”。

    因此，出于这些原因，我们希望有一种更精细化的方式来定义和推理程序的行为。这便是本章的话题。
    我们的目的是用“小步（small-step）”关系来代替“大步（big-step）”的 [eval] 关系，
    前者对于给定的程序，描述了计算是如何以“不可分步骤（atomic steps）”执行的。 *)

(* ################################################################# *)
(** * 一个玩具语言 *)

(** 为了简化讨论，让我们回过头来考虑一个只含有常量和加法的简单语言。
    （我们使用字母——[C] 和 [P]（代表常量（Constant）和加法（Plus）——
    简洁地作为构造子的名字。）在本章的最后，我们回看到如何将这些技术应用到
    Imp 语言上。*)

Inductive tm : Type :=
  | C : nat -> tm         (* 常量 *)
  | P : tm -> tm -> tm.   (* 加法 *)

(** 这是我们之前学习的大步语义风格求值器。 *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

(** 这是用同样风格描述的等价求值器，只是用归纳关系来定义。
    我们使用记号 [t ==> n] 来表达“[t] 求值到 [n]”。 

                               ---------                               (E_Const)
                               C n ==> n

                               t1 ==> n1
                               t2 ==> n2
                           -------------------                         (E_Plus)
                           P t1 t2 ==> n1 + n2
*)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)
where " t '==>' n " := (eval t n).

Module SimpleArith1.

(** 现在，我们展示对应的_'小步'_求值关系。 

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_Plus2)
                      P (C n1) t2 --> P (C n1) t2'
*)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

(** 值得注意的几点：

    - 我们定义的仅仅是单步关系，其中只有一个 [P] 节点被其值替换。

    - 每步找到准备好的_'最左侧（leftmost）'_ [P] 节点（也即其操作数都是常量），
      并在原地重写它。第一个规则是说如何重写 [P] 节点自己；剩下的两个是说如何
      得到这样的 [P]。

    - 一个常量项无法继续被求值。 *)

(** 让我们暂停一下，并使用 [step] 关系来推理一些例子…… *)

(** 如果 [t1] 可向前一步到 [t1']，那么 [P t1 t2] 可向前一步到 [P t1' t2]: *)

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

(** **** 练习：1 星, standard (test_step_2)  

    当求和操作的左侧表达式已经完成求值，其右侧表达式可向前一步：
    如果 [t2] 可向前一步到 [t2']，那么 [P (C n) t2] 可向前一步到 [P (C n) t2']： *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

End SimpleArith1.

(* ################################################################# *)
(** * 关系 *)

(** 我们将会研究多个不同的单步关系，因此泛化一下这个概念，给出一些关系的一般定义和
    定理是十分有帮助的。（可选章 [Rel.v] 以更细致的方式开发了这个想法；放在这里
    可能会对读者有帮助，但内容过于密集。）

    集合 [X] 上的_'二元关系（binary relation）'_是由 [X] 中的两个元素参数化的
    命题——也即，一个 [X] 上序对的命题。 *)

Definition relation (X : Type) := X -> X -> Prop.

(** 本章中，我们主要的例子将会是单步规约关系，[-->]，以及它的多步版本，
    [-->*]（后面会定义），但是也有许多其他例子——比如，“等于”、“小于”、“小于等于”
    和数字上“平方数”关系，还有字符串和列表的“前缀”关系。*)

(** 和 Imp 的大步求值关系一样，[-->] 关系的一个简单性质是_'确定性（deterministic）'_。

    _'定理'_：对于每个 [t]，最多有一个 [t'] 且 [t] 向前一步到 [t']
     ([t --> t'] 是可证的)。这也就是说 [-->] 是确定性的。*)

(** _'证明草稿'_：我们通过对 [step x y1] 的导出式（derivation）进行归
    纳来证明如果 [x] 同时前进到 [y1] 和 [y2]，那么 [y1] 和 [y2] 是相等的。
    取决于导出式中最后使用的规则和 [step x y2] 的导出式中最后的规则，我们有许多
    情形需要考虑。

      - 如果二者皆为 [ST_PlusConstConst]，那么结果是显然的。

      - 对于两个导出式都以 [ST_Plus1] 或 [ST_Plus2] 结束的情形，可直接从归纳假设中得证。

      - 其中一个是 [ST_PlusConstConst] 同时另一个是 [ST_Plus1] 或 [ST_Plus2]
        的情形是不可能发生的，因为这蕴含了 [x] 形如 [P t1 t2] 而 [t1] 和 [t2]
        都是常量（根据 [ST_PlusConstConst]）_'且'_ [t1] 或 [t2] 中的一个形如
        [P _]。

      - 类似地，一个是 [ST_Plus1] 同时另一个是 [ST_Plus2] 的情形也不可能发生，
        因为这蕴含了 [x] 形如 [P t1 t2] 而 [t1] 同时是 [P t11 t12] 和 [C n]
        两种形式。 []  *)

(** 形式化地来说： *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PlusConstConst *) inversion Hy2.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2.
    + (* ST_PlusConstConst *)
      rewrite <- H0 in Hy1. inversion Hy1.
    + (* ST_Plus1 *)
      rewrite <- (IHHy1 t1'0).
      reflexivity. assumption.
    + (* ST_Plus2 *)
      rewrite <- H in Hy1. inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2.
    + (* ST_PlusConstConst *)
      rewrite <- H1 in Hy1. inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      rewrite <- (IHHy1 t2'0).
      reflexivity. assumption.
Qed.

End SimpleArith2.

(** 可以看到在证明中有一些繁琐的重复。每次使用 [inversion Hy2] 会产生
    三个子情形，但只有一个是相关的（匹配当前对 [Hy1] 归纳的那个情形）。
    剩下的两个子情形需要通过从假设中找到矛盾并对其反演来消解掉。

    下面自定义一个叫做 [solve_by_inverts] 的策略可以简化这些情形。
    如果目标可以通过反演某些假设来解决，调用 [solve_by_inverts] 会证明目标；
    否则，它会失败。 *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

(** 关于它是如何工作的细节目前不那么重要，但是它展示了 Coq 中 [Ltac]
    语言的能力以及如何编写特殊目标的策略。它会在当前证明状态中找到一个具有类型
    [Prop] （第二个 [match]）的假设 [H]（第一个 [match]），然后对 [H]
    进行反演（如果参数 [n] 大于一，那么它会继续递归地调用这个策略）来完成当前目标。
    如果这样的假设不存在，这个策略会失败。

    我们通常会带上参数 [1] 来调用 [solve_by_inverts]（特别是很大的参数会导致
    长时间的证明检查），因此我们对它定义一个缩写 [solve_by_invert]。 *)

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** 让我们看看这个策略如何简化之前定理的证明吧…… *)

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

(* ================================================================= *)
(** ** 值 *)

(** 下一步，我们会使用“值”的概念来稍微重新表述一下单步归约的定义。*)

(** 为了更好地理解 [-->] 关系，我们定义一个_'抽象机（abstract machine）'_:

      - 在任意时刻，机器的_'状态（state）'_是一个项（term）。

      - 机器的一_'步（step）'_是一个原子单元的计算，在这里，是一个“加法”操作。

      - 机器的_'停机状态（halting states）'_是指没有后继计算的状态。 *)

(** 我们可以通过以下方式来执行项 [t]：

      - 以 [t] 作为机器的起始状态。

      - 重复使用 [-->] 关系来找到一个以 [t] 开始的机器状态序列，序列中每个状态
        会转移到下一个。

      - 当无法继续进行归约时，_'输出（read out）'_最终的机器状态作为执行的结果。  *)

(** 直观地来说，可以看到机器的最终状态总是形如 [C n] 的项。
    我们把这些项叫做_'值（values）'_。 *)

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

(** 在引入了值的概念后，我们可以使用它来更简洁地定义 [-->]
    关系中的 [ST_Plus2] 规则： *)

(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 --> P v1 t2'

    再一次地，变量名在这里包含了重要的信息：按照惯例，[v1] 涉及到值，
    而 [t1] 和 [t2] 涉及到任意的项。（在这种约定下，显式的 [value] 假设也
    许是多余的。在这里仍然保留它，主要是为了在非形式化的和 Coq 的规则之间
    建立起密切的对应关系，但为简单起见，后面的非形式化规则中我们便会省略掉它。） *)

(**  这些是形式化的规则： *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(** **** 练习：3 星, standard, recommended (redo_determinism)  

    作为这一改变的完备性检查，让我们重新验证一下确定性。
    下面是它的非形式化证明：

    _'证明草稿'_：我们必须证明如果 [x] 向前一步可同时到 [y1] 和 [y2]，
    那么 [y1] 和 [y2] 相等。考虑 [step x y1] 和 [step x y2] 生成式
    中最后使用的规则。

    - 如果二者皆为 [ST_PlusConstConst]，那么结果是显然的。

    - 其中一个是 [ST_PlusConstConst] 同时另一个是 [ST_Plue1] 或 [ST_Plus2]
      的情形是不可能发生的，因为这蕴含了 [x] 形如 [P t1 t2] 而 [t1] 和 [t2]
      都是常量_'且'_ [t1] 或 [t2] 中的一个形如 [P _]。

    - 类似地，一个是 [ST_Plus1] 同时另一个是 [ST_Plus2] 的情形也不可能发生，
      因为这蕴含了 [x] 形如 [P t1 t2] 而 [t1] 既形如 [P t11 t12] 又是值
      （因此形如 [C n]）。

    - 对于两个导出式都以 [ST_Plus1] 或 [ST_Plus2] 结束的情形，可直接从归纳假设中得证。[] *)

(** 本证明中大部分与之前的相同。但为了最大化练习的收益，你应该从零写下形式化的版本，
    只有当卡住时再去回顾之前的证明。 *)

Theorem step_deterministic :
  deterministic step.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 强可进性和正规式 *)

(** 这个玩具语言的单步归约定义是十分简单的，但是对于大一点的语言，往往会出现
    因为忘记某个规则而导致一些项虽然还不是值但已无法继续前进归约的情况。下面的定理
    说明了我们没有犯这样的错误。 *)

(** _'定理'_（_'强可进性'_（Strong Progress））：如果 [t] 是一个项，那么 [t]
    要么是一个值，要么存在项 [t'] 使 [t --> t']。*)

(** _'证明'_：对 [t] 进行归纳。

    - 假设 [t = C n]。那么 [t] 是值。

    - 假设 Suppose [t = P t1 t2]，其中 [t1] 或是值，或可前进到某个 [t1']；
      [t2] 或是值，或可前进到某个 [t2']（根据 [IH]）。我们需要证明 [P t1 t2] 要么是值，
      要么可前进到某个 [t']

      - 如果 [t1] 和 [t2] 都是值，那么根据 [ST_PlusConstConst] 得 [t] 可前进一步。

      - 如果 [t1] 是值且 [t2] 可前进一步，那么根据 [ST_Plus2] 得 [t] 可前进一步。

      - 如果 [t1] 可前进一步，那么根据 [ST_Plus1] 得 [t] 可前进一步。 []

   或者，形式化地说： *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C *) left. apply v_const.
  - (* P *) right. destruct IHt1 as [IHt1 | [t1' Ht1]].
    + (* l *) destruct IHt2 as [IHt2 | [t2' Ht2]].
      * (* l *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      * (* r *)
        exists (P t1 t2').
        apply ST_Plus2. apply IHt1. apply Ht2.
    + (* r *)
      exists (P t1' t2).
      apply ST_Plus1. apply Ht1.
Qed.

(** 这个重要的定理叫做_'强可进性（strong progress）'_，因为每个项
    要么是值，要么可“前进”到某个其他的项。（修饰语“强”区分另一个不同的版本，
    叫做_'可进性'_，我们在后面的章节中会学校到。） *)

(** 通过扩展“做出前进”这个概念，我们可以得到一些关于值有趣的事实：在本语言中，
    从这个意义上讲，值是_'不能'_够继续前进的项。

    为了形式化地表述这个观察，让我们给不能前进的项起个名字。我们把它叫做
    _'正规式（normal forms）'_。 *)

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(** 请注意这个定义规范了对任意集合 [X] 上的任意关系 [R] 的正规式，而不仅仅是我们
    这里关心的某个单步归约关系的正规式。后面的课程讨论其他关系时我们会继续使用这个术语。 *)

(** 我们可以使用这个术语来一般化对于强可进性定理的观察：在这个语言中，
    正规式和值实际上是同一个东西。 *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

(** 这个为什么值得注意呢？

    因为 [value] 是一个语法概念——它是由项的形式定义的——然而 [normal_form] 是一个
    语义概念——它是由项如何前进定义的。

    并不显然这两个概念应当一致！ *)

(** 确实，容易错误地写下使它们_'不'_一致的定义。 *)

(** **** 练习：3 星, standard, optional (value_not_same_as_normal_form1)  

    我们可能错误地定义了 [value] 使它包括了还没有完成归约的项。 

    （如果你不想亲自动手在 Coq 中完成这个和下一个练习，
    也请思考一下，尝试找到一个这样的项。）*)

Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2,
                value (P t1 (C n2)).              (* <--- *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* 请在此处解答 *) Admitted.
End Temp1.

(** [] *)

(** **** 练习：2 星, standard, optional (value_not_same_as_normal_form2)  

    或许，我们错误地定义了 [step] 使它允许继续归约一个值。 *)

Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).         (* Original definition *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* 请在此处解答 *) Admitted.

End Temp2.
(** [] *)

(** **** 练习：3 星, standard, optional (value_not_same_as_normal_form3)  

    最后，我们还可能通过 [value] 和 [step] 定义了某些不是值但已无法继续由
    [step] 关系进行归约的项。这些项被称作_'卡住了（stuck）'_。在这种情况是由语义
    中的错误导致的，但我们也会看到一些情况，即使是正确的语言定义中也会允许一些项卡住。 *)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

(** （请注意 [ST_Plus2] 是未定义的。） *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* 请在此处解答 *) Admitted.

End Temp3.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 额外练习 *)

Module Temp4.

(** 这是另一个非常简单的语言，其项并不是数字和加法表达式，而是布尔值真和假，
    以及条件表达式…… *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(** **** 练习：1 星, standard (smallstep_bools)  

    下列哪些命题是可被证明的？（这只是一个思考练习，但如果你想挑战一下自己，
    可以尝试在 Coq 中证明你的答案。） *)

Definition bool_step_prop1 :=
  fls --> fls.

(* 请在此处解答 *)

Definition bool_step_prop2 :=
     test
       tru
       (test tru tru tru)
       (test fls fls fls)
  -->
     tru.

(* 请在此处解答 *)

Definition bool_step_prop3 :=
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_smallstep_bools : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, standard, optional (progress_bool)  

    我们之前对加法表达式证明了其可进性，我们也可以证明布尔表达式的可进性。 *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (step_deterministic)  *)
Theorem step_deterministic :
  deterministic step.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

Module Temp5.

(** **** 练习：2 星, standard (smallstep_bool_shortcut)  

    假设我们想要为布尔表达式的单步归约关系添加“短路（short circuit）”，
    这样当条件语句的 [then] 和 [else] 分支有相同的值时（[tru] 或 [fls]），
    便可以用一步化简整个条件表达式到值，尽管其条件还没有被归约到某个值。
    比如，我们想要下面的命题可被证明：

         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.
*)

(** 请为单步关系添加一个额外的语句来达到这个目的，并证明 [bool_step_prop4]。 *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  (* 请在此处解答 *)

  where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (properties_of_altered_step)  

    课程中证明的确定性和强可进性定理对于我们刚刚定义的单步关系也是成立的。
    在我们添加了 [ST_ShortCircuit] 以后……

    - [step] 关系是否仍然是确定的？请回答是或否，并简要解释（一句话即可）你的答案。

      可选：在 Coq 中证明你的答案。*)

(* 请在此处解答 
   - 强可进性是否成立？请回答是或否，并简要解释（一句话即可）你的答案。

     可选：在 Coq 中证明你的答案。
*)

(* 请在此处解答 
   - 一般来说，如果从原始的单步关系中拿掉一两个构造子，能否使强可进性不再成立？
     请回答是或否，并简要解释（一句话即可）你的答案。

(* 请在此处解答 *)

    [] *)

End Temp5.
End Temp4.

(* ################################################################# *)
(** * 多步归约 *)

(** 目前为止，我们学习的是_'单步归约（single-step reduction）'_关系 [-->]，
    它形式化了抽象机执行程序的每一步。

    我们可以使用同一个机器来归约程序直到结束——得到它最后的结果。我们这样形式化它：

    - 首先，我们定义一个_'多步归约关系（multi-step reduction relation）'_
      [-->*]，如果项 [t] 可在任意多的单步（包括零步）内到达 [t']，那么它关联起
      [t] 和 [t']。

    - 接着我们定义 [t] 的“结果（result）”是一个 [t] 可用多步达到的正规式。*)

(** 因为我们会反复使用多步归约这个概念，让我们花点功夫一般化地定义它。

    如下，给定关系 [R]（当前为 [-->]），我们定义关系 [multi R] 是 [R]
    的_'多步闭包（multi-step closure）'_。*)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** （在_'逻辑基础'_的 [Rel] 一章和 Coq 标准库中，这个关系叫做
    [clos_refl_trans_1n]。出于可读性的考虑，我们给出一个简短的名字。） *)

(** 这个定义的作用是 [multi R] 关联起两个元素 [x] 和 [y]，如果

       - [x = y]，或
       - [R x y]，或
       - 存在某个非空序列 [z1],[z2], ..., [zn] 使得

           R x z1
           R z1 z2
           ...
           R zn y.

    因此，如果 [R] 刻画了单步计算，那么 [z1] ... [zn] 则是 [x] 和 [y]
    的中间计算步骤。 *)

(** 我们为关系 [multi step] 使用记号 [-->*]。*)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** 关系 [multi R] 具有多个重要的性质。

    首先，显然它是_'自反的（reflexive）'_（即 [forall x, multi R x x]）。
    就 [-->*] 关系（即 [multi step]）而言，可以直观地理解为一个项可以执行零步
    到它自己。 *)

(** 第二，它包含了 [R]——也即，单步执行是多步执行的一个特殊情况。（这个事实解释了
    “[R] 的多步闭包（multi-step closure）”中的“闭包（closure）”一词。） *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

(** 第三， [multi R] 是_'传递的（transitive）'_。 *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

(** 特别地，对于项的 [multi step] 关系可得，如果 [t1 -->* t2] 且 [t2 -->* t3]，
    那么 [t1 -->* t3]。*)

(* ================================================================= *)
(** ** 例子 *)

(** 这里有一些 [multi step] 关系的例子： *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_Plus1. apply ST_PlusConstConst. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  apply multi_R.
  { apply ST_PlusConstConst. }
Qed.

(** 这是使用 [eapply] 的另一种证明方法，可以避免显式地构造所有的中间项。 *)

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const.
                       apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
Qed.

(** **** 练习：1 星, standard, optional (test_multistep_2)  *)
Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (test_multistep_3)  *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 再谈正规式 *)

(** 如果 [t] 可在零步或多步归约到 [t'] 且 [t'] 是一个正规式，那么我们说
    “[t'] 是 [t] 的一个正规式”。 *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

(** 我们已经看到，这这个语言中，单步归约是确定的——也即，给定的项最多只有一种方法
    前进一步。从中可推论，如果 [t] 可以到到某个正规式，那么这个正规式唯一。换句话说，
    我们实际上可以把 [normal_form t t'] 理解为“[t'] _'就是'_ [t] 的正规式”。*)

(** **** 练习：3 星, standard, optional (normal_forms_unique)  *)
Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* 我们推荐以这样的方式开始证明。 *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 确实，这个语言中还具备更强的性质（尽管不是所有语言都具备）：
    任意项 [t] 最终都会到达一个正规式——即，[normal_form_of] 是一个全函数。
    形式化地讲，我们说 [step] 关系是_'正规化（normalizing）'_的。 *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

(** 为了证明 [step] 的正规性，我们需要几个引理。

    首先，我们观察到如果 [t] 以多步归约到 [t']，那么当 [t] 出现为 [P] 节点的左子节点时，
    可以使用同一个 [t] 的归约序列。同理，当 [P] 的左子节点为值时，若 [t] 出现为 [P]
    的右子节点也适用。 *)

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.

(** **** 练习：2 星, standard (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     P t1 t2 -->* P t1 t2'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 使用这些引理，证明的主体是直接进行归纳。

    _'定理'_：[step] 函数是正规化的——即，对于每个 [t] 存在某个 [t'] 使
    [t] 前进到 [t']，且 [t'] 是正规式。

    _'证明草稿'_：对项进行归纳。有两个情形需要考虑：

    - [t = C n] 其中 [n] 为数字。这里 [t] 无法前进一步，我们有 [t' = t]。
      我们可以通过自反性证明左手边的项；对于右手边的项，由 [nf_same_as_value]
      可得值是正规式，且由 [v_const] 可得 [t] 是一个值。

    - [t = P t1 t2] 其中 [t1] 和 [t2] 为项。由归纳假设，[t1] 和 [t2]
      分别有正规式 [t1'] 和 [t2']。回忆一下正规式是值（由 [nf_same_sa_value]）；
      我们知道 [t1' = C n1] 和 [t2' = C n2] 其中 [n1] 和 [n2] 为项。
      我们可以使用 [multi_congr_1] 和 [multi_congr_2] 合并 [t1] 和 [t2]
      的 [-->*] 导出式，以此证明 [P t1 t2] 在多步内归约到 [C (n1 + n2)]。

      显然，我们的选择 [t' = C (n1 + n2)] 是一个值，也是一个正规式。[] *)

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
        (* 除了等式，对于当且进当的命题，我们也可以使用 [rewrite]。 *)
      rewrite nf_same_as_value. apply v_const.
  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1]].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2]].
    rewrite nf_same_as_value in Hnormal1.
    rewrite nf_same_as_value in Hnormal2.
    inversion Hnormal1 as [n1 H1].
    inversion Hnormal2 as [n2 H2].
    rewrite <- H1 in Hsteps1.
    rewrite <- H2 in Hsteps2.
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with
        (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply Hsteps2. }
        apply multi_R. { apply ST_PlusConstConst. }
    + (* r *)
      rewrite nf_same_as_value. apply v_const.
Qed.

(* ================================================================= *)
(** ** 大步语义和小步语义的等价关系 *)

(** 在使用两种不同的方式（大步和小步式）定义了这个小小语言的操作语义后，你可能会
    好奇这两种定义是否是等价的！他们确实是，尽管需要一点工作来证明它。
    具体细节留做了练习。*)

(** **** 练习：3 星, standard (eval__multistep)  *)
Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** 证明的核心想法以下面的方式展现：

       P t1 t2 -->            (by ST_Plus1)
       P t1' t2 -->           (by ST_Plus1)
       P t1'' t2 -->          (by ST_Plus1)
       ...
       P (C n1) t2 -->        (by ST_Plus2)
       P (C n1) t2' -->       (by ST_Plus2)
       P (C n1) t2'' -->      (by ST_Plus2)
       ...
       P (C n1) (C n2) -->    (by ST_PlusConstConst)
       C (n1 + n2)

    也即，一个形如 [P t1 t2] 的项的多步归约关系以如下三步的方式进行：
       - 首先，使用 [ST_Plus1] 数次来归约 [t1] 到正规式，也即必须是一个形如 [C n1]
         的项（由 [nf_same_as_value]），其中 [n1] 为某个数字。

       - 接着，使用 [ST_Plus2] 数次来归约 [t2] 到正规式，也即必须是一个形如 [C n2]
         的项，其中 [n2] 为某个数字。

       - 最后，使用 [ST_PlusConstConst] 一次把 [P (C n1) (C n2)] 归约到
         [C (n1 + n2)]。*)

(** 为了形式化这个直觉的理解，我们需要使用之前的合同（congruence）引理
    （为了帮助后面的证明，你可能需要回顾一下他们），还有一些 [-->*] 的基础性质：
    自反性，传递性，及其蕴含了 [-->]。 *)

Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (eval__multistep_inf)  

    请为 [eval__multi_step] 写出详细的非形式化证明。

(* 请在此处解答 *)
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_eval__multistep_inf : option (nat*string) := None.
(** [] *)

(** 对于另一个方向，我们需要一个引理来对单步归约和大步求值建立联系。*)

(** **** 练习：3 星, standard (step__eval)  *)
Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 一旦正确地表述了小步归约蕴含了大步求值的事实，它会很容易被证明。

    证明是对多步归约序列的归纳，这个序列被假设 [normal_form_of t t']
    所隐藏了起来。*)

(**请确保在开始证明前首先理解了命题。 *)

(** **** 练习：3 星, standard (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 额外练习 *)

(** **** 练习：3 星, standard, optional (interp_tm)  

    请回忆一下我们还通过函数 [evalF] 定义了对项的大步求值。请证明它等价于其他语义。
    （提示：我刚刚证明了 [eval] 和 [multistep] 是等价的，因此逻辑上讲你可以任意
    选择证明哪个。尽管有一个要比另一个简单！） *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard (combined_properties)  

    我们分开考虑了算数和条件表达式，这个练习探索了他们之间如何交互。 *)

Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(** 之前，我们分开证明了加法和条件表达式的……

    - 单步关系是确定的，以及

    - 一个强可进行引理，陈述了任意项要么是值，要么可以前进一步。

    对于合并起来的语言，请形式化地证明或反驳这两个属性。
    （也即，陈述定理表达性质成立或不成立，并证明它们。） *)

(* 请在此处解答 *)

End Combined.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_combined_properties : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Imp 的小步语义 *)

(** 现在来看一个更严肃的例子：Imp 的小步操作语义。 *)

(** 目前为止，给这个小语言添加算数和布尔表达式的小步归约关系是很直接的扩展。
    处于可读性的考虑，我们为他们分别添加记号 [-->a] 和 [-->b]。 *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** 我们在此不会赘述布尔值的定义，因为 [-->b] 的定义并不需要他们（为什么？），
    尽管当语言规模更大一些时可能会需要到他们（为什么？）。*)

Reserved Notation " t '/' st '-->a' t' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

    where " t '/' st '-->a' t' " := (astep st t t').

Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
    b1 / st -->b b1' ->
    (BNot b1) / st -->b (BNot b1')
| BS_NotTrue : forall st,
    (BNot BTrue) / st -->b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st -->b BTrue
| BS_AndTrueStep : forall st b2 b2',
    b2 / st -->b b2' ->
    (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st -->b b1' ->
    (BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st -->b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st -->b BFalse

where " t '/' st '-->b' t' " := (bstep st t t').

(** 命令的语义是真正有趣的部分。我们需要两个小技巧来让们工作：

       - 我们把 [SKIP] 当作一个“命令值（command value）”——即，一个已经到达正规式的命令。

            - 赋值命令归约到 [SKIP] （和一个更新状态）。

            - 顺序命令等待其左侧子命令归约到 [SKIP]，然后丢弃它，并继续
              对右侧子命令归约。

       - 对 [WHILE] 命令的归约是把 [WHILE] 命令变换为条件语句，其后紧跟同一个
         [WHILE] 命令。 *)

(** （也有一些其他的方式来达到后一个技巧同样的效果，但当对循环体进行归约时，
    他们都需要将原始的 [WHILE] 命令保存在某处。）*)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Open Scope imp_scope.
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      TEST b  THEN c1 ELSE c2 FI / st
      -->
      (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      TEST BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      TEST BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : forall st b c1,
      WHILE b DO c1 END / st
      -->
      (TEST b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Close Scope imp_scope.

(* ################################################################# *)
(** * 并发 Imp *)

(** 最后，为了展示这种定义方式的能力，让我们为 Imp 语言添加一个新的命令，
    使其可以同时运行两个命令，并在两个都停机时停机。为了反映调度的不可预测性，
    子命令可以以任意顺序交错运行，但他们共享了同一个内存，并以读写变量的方式通信。 *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st -->b b' ->
          (TEST b THEN c1 ELSE c2 FI) / st
      --> (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      (TEST BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (TEST BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      --> (TEST b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st --> SKIP / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(** 在这个语言的众多特性中，一个有趣的事实是下面的程序在停机时变量 [X] 可以是任何值。*)

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END.

(** 比如说，它可以当 [X] 为 [0] 时停机。*)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** 它也可以当 [X] 为 [2] 时停机。*)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** 更一般地…… *)

(** **** 练习：3 星, standard, optional (par_body_n__Sn)  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (par_body_n)  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** ……上面的循环可以在 [X] 为任何值时退出。 *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_st).
    split; unfold t_update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H.
  exists (Y !-> 1 ; st). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

End CImp.

(* ################################################################# *)
(** * 小步堆栈机 *)

(** 最后一个例子来自逻辑基础的 [Imp] 一章，我们给出堆栈机的小步语义。 *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(** **** 练习：3 星, advanced (compiler_is_correct)  

    请回忆一下_'逻辑基础'_ [Imp] 一章中对 [compile] 和 [aexp] 的定义。
    我们现在想要证明堆栈机上 [s_compile] 函数的正确性。

    请根据堆栈机的小步语义陈述编译器正确性的定义，并证明它。 *)

Definition compiler_is_correct_statement : Prop
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Aside: A [normalize] Tactic *)

(** When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t -->*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation [astep]. *)

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

(** The proof repeatedly applies [multi_step] until the term reaches a
    normal form.  Fortunately The sub-proofs for the intermediate
    steps are simple enough that [auto], with appropriate hints, can
    solve them. *)

Hint Constructors step value.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
  (* The [print_goal] in the [normalize] tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) -->* C 10)
         (P (C 3) (C 7) -->* C 10)
         (C 10 -->* C 10)
  *)
Qed.

(** The [normalize] tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eapply ex_intro. normalize.
(* This time, the trace is:
       (P (C 3) (P (C 3) (C 4)) -->* ?e')
       (P (C 3) (C 7) -->* ?e')
       (C 10 -->* ?e')
   where ?e' is the variable ``guessed'' by eapply. *)
Qed.

(** **** 练习：1 星, standard (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (normalize_ex')  

    For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* Fri Jul 19 00:33:14 UTC 2019 *)
