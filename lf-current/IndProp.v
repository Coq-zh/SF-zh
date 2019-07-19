(** * IndProp: 归纳定义的命题 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

(* ################################################################# *)
(** * 归纳定义的命题 *)

(** 在 [Logic] 一章中，我们学习了多种方式来书写命题，包括合取、析取和存在量词。
    在本章中，我们引入另一种新的方式：_'归纳定义（Inductive Definitions）'_。 *)

(** 在前面的章节中，我们已经见过两种表述 [n] 为偶数的方式了：

      (1) [evenb n = true]，以及

      (2) [exists k, n = double k]。

    然而还有一种方式是通过如下规则来建立 [n] 的偶数性质：

       - 规则 [ev_0]: [0] 是偶数。
       - 规则 [ev_SS]: 如果 [n] 是偶数, 那么 [S (S n)] 也是偶数。 *)

(** 为了理解这个新的偶数性质定义如何工作，我们可想象如何证明 [4] 是偶数。
    根据规则 [ev_SS]，需要证明 [2] 是偶数。这时，只要证明 [0] 是偶数，
    我们可继续通过规则 [ev_SS] 确保它成立。而使用规则 [ev_0] 可直接证明 [0] 是偶数。*)

(** 接下来的课程中，我们会看到很多类似方式定义的命题。
    在非形式化的讨论中，使用轻量化的记法有助于阅读和书写。
    _'推断规则（Inference Rules）'_是其中的一种： 

                              ------------             (ev_0)
                                 even 0

                                 even n
                            ----------------          (ev_SS)
                             even (S (S n))
*)

(**
    若将前文所述的规则重新排版成推断规则，我们可以这样阅读它，如果线上方的
    _'前提（premises）'_成立，那么线下方的_'结论（conclusion）'_成立。
    比如，规则 [ev_SS] 读做如果 [n] 满足 [even]，那么 [S (S n)] 也满足。
    如果一条规则在线上方没有前提，则结论直接成立。

    我们可以通过组合推断规则来展示证明。下面展示如何转译 [4] 是偶数的证明： 

                             --------  (ev_0)
                              even 0
                             -------- (ev_SS)
                              even 2
                             -------- (ev_SS)
                              even 4
*)

(**
    （为什么我们把这样的证明称之为“树”（而非其他，比如“栈”）？
    因为一般来说推断规则可以有多个前提。我们很快就会看到一些例子。 *)

(* ================================================================= *)
(** ** 偶数性的归纳定义 

    基于上述，可将偶数性质的定义翻译为在 Coq 中使用 [Inductive] 声明的定义，
    声明中每一个构造子对应一个推断规则： *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(** 这个定义同之前其他 [Inductive] 的使用有一个重要的区别：
    我们所定义的并不是一个 [Type]，而是一个将 [nat] 映射到 [Prop] 的函数——即关于数的性质。
    我们曾见过结果也是函数的归纳定义，比如 [list]，其类型是 [Type -> Type] 。
    真正要关注的是，由于 [even] 中出现在冒号_'右侧'_的 [nat] 参数是 _'未命名'_ 的，
    这允许在不同的构造子类型中使用不同的值：例如 [ev_0] 类型中的 [0] 以及 [ev_SS]
    类型中的 [S (S n)]。

    相反，[list] 的定义以_'全局方式'_命名了冒号_'左侧'_的参数 [X]，
    强迫 [nil] 和 [cons] 的结果为同一个类型（[list X]）。
    如果在定义 [even] 时我们将 [nat] 置于冒号左侧，会得到如下错误： *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** 在 [Inductive] 定义中，类型构造子的冒号左侧的参数叫做形参（Parameter），
    而右侧的叫做索引（Index）。

    例如，在 [Inductive list (X : Type) := ...] 中，[X] 是一个形参；而在
    [Inductive even : nat -> Prop := ...] 中，未命名的 [nat] 参数是一个索引。 *)

(** 在 Coq 中，我们可以认为 [even] 定义了一个性质 [ev : nat -> Prop]，其包括原语定理
    [ev_0 : even 0] 和 [ev_SS : forall n, even n -> even (S (S n))]。 *)

(** 该定义也可写作如下形式...

  Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n, even n -> even (S (S n)).
*)

(** ... 以便让 [ev_SS] 的类型更加直白。 *)

(** 这些 “定理构造子” 等同于已经证明过的定理。
    具体来说，我们可以使用 Coq 中的 [apply] 策略和规则名称来证明某个数的 [even] 性质…… *)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ……或使用函数应用的语法： *)

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** 我们同样可以对前提中使用到 [even] 的定理进行证明。 *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** 更一般地，我们可以证明以任意数乘 2 是偶数： *)

(** **** 练习：1 星, standard (ev_double)  *)
Theorem ev_double : forall n,
  even (double n).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 在证明中使用证据 *)

(** 除了_'构造'_证据（evidence）来表示某个数是偶数，我们还可以对这些证据进行_'推理'_。

    对 [even] 而言，使用 [Inductive] 声明来引入 [even] 不仅仅表示在 Coq
    中 [ev_0] 和 [ev_SS] 这样的构造子是合法的方式来构造偶数证明的证据，
    他们也是_'仅有的'_方式。 *)

(** 换句话说，如果某人展示了对于 [even n] 的证据 [E]，那么我们知道 [E]
    必是二者其一：

      - [E] 是 [ev_0]（且 [n] 为 [O]）, 或
      - [E] 是 [ev_SS n' E']（且 [n] 为 [S (S n')], [E'] 为
        [even n'] 的证据）. *)

(** 这样的形式暗示着，我们可以像分析归纳定义的数据结构一样分析形如 [even n]
    的假设；特别地，对于这类证据使用_'归纳（induction）'_和_'分类讨论（case
    analysis）'_来进行论证也是可行的。让我们通过一些例子来学习实践中如何使用他们。 *)

(* ================================================================= *)
(** ** 对证据进行反演 *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [even n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [even n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [even n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** 用 [destruct] 解构证据即可证明下述定理： *)

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with [destruct]. *)

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
(** 直观来说，我们知道支撑前提的证据不会由 [ev_0] 组成，因为 [0] 和 [S] 是
    [nat] 类型不同的构造子；由此 [ev_SS] 是唯一需要应对的情况（译注：[ev_0] 无条件成立）。
    不幸的是，[destruct] 并没有如此智能，它仍然为我们生成两个子目标。
    更坏的是，于此同时最终目标没有改变，也无法为完成证明提供任何有用的信息。 *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* 我们须证明 [n] 是偶数，但没有任何有用的假设信息可以使用！ *)
Abort.

(** 究竟发生了什么？应用 [destruct] 把性质的参数替换为对应于构造子的值。
    这对于证明 [ev_minus2'] 是有帮助的，因为在最终目标中直接使用到了参数 [n]。
    然而，这对于 [evSS_ev] 并没有帮助，因为被替换掉的 [S (S n)] 并没有在其他地方被使用。*)

(** We could patch this proof by replacing the goal [even n],
    which does not mention the replaced term [S (S n)], by the
    equivalent goal [even (pred (pred (S (S n))))], which does mention
    this term, after which [destruct] can make progress. But it is
    more straightforward to use our inversion lemma. *)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(** Coq provides a tactic called [inversion], which does the work of
    our inversion lemma and more besides. *)

(** The [inversion] tactic can detect (1) that the first case
    ([n = 0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)
Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

(** **** 练习：1 星, standard (inversion_practice)  

    利用 [inversion] 策略证明以下结论。如想进一步练习，请使用反演定理证明之。 *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (even5_nonsense)  

    请使用 [inversion] 策略证明以下结果。 *)

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** The [inversion] tactic does quite a bit of work. When
    applied to equalities, as a special case, it does the work of both
    [discriminate] and [injection]. In addition, it carries out the
    [intros] and [rewrite]s that are typically necessary in the case
    of [injection]. It can also be applied, more generally, to analyze
    evidence for inductively defined propositions.  As examples, we'll
    use it to reprove some theorems from [Tactics.v]. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** [inversion] 的工作原理大致如下：假设 [H] 指代上下文中的假设 [P]，
    且 [P] 由 [Inductive] 归纳定义，则对于 [P] 每一种可能的构造，[inversion H]
    各为其生成子目标。子目标中自相矛盾者被忽略，证明其余子命题即可得证原命题。
    在证明子目标时，上下文中的 [H] 会替换为 [P] 的构造条件，
    即其构造子所需参数以及必要的等式关系。例如：倘若 [ev n] 由 [evSS] 构造，
    上下文中会引入参数 [n']、[ev n']，以及等式 [S (S n') = n]。 *)

(** 上面的 [ev_double] 练习展示了偶数性质的一种新记法，其被之前的两种记法所蕴含。
    （因为，由  [Logic] 一章中的 [even_bool_prop]，我们已经知道
    他们是互相等价的。）
    为了展示这三种方式的一致性，我们需要下面的引理： *)

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
(* 课上已完成 *)

(** 我们可以尝试使用分类讨论或对 [n] 进行归纳。
    但由于 [even] 在前提中出现，如同之前章节的一些例子，这种策略或许无法行得通。
    如此我们似乎可以首先尝试对 [even] 的证据进行反演。
    确实，第一个分类可以被平凡地证明。 *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** 不幸地是，第二个分类要困难一些。我们需要证明 [exists k, S (S n') = double k]，
    但唯一可用的假设是 [E']，也即 [even n'] 成立。但这对证明并没有帮助，
    我们似乎被卡住了，而对 [E] 进行分类讨论是徒劳的。

    如果仔细观察第二个（子）目标，我们可以发现一些有意思的事情：
    对 [E] 进行分类讨论，我们可以把要证明的原始目标归约到另一个上，
    其涉及到另一个 [even] 的证据： [E']。
    形式化地说，我们可以通过展示如下证据来完成证明：

        exists k', n' = double k',

    这同原始的命题是等价的，只是 [n'] 被替换为 n。确实，通过这个中间结果完成证明
    并不困难。  *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* 将原始目标归约到新目标上 *)

Abort.

(* ================================================================= *)
(** ** 对证据进行归纳 *)

(** 在 [Induction] 一章中，我们曾尝试使用分类讨论来证明其实需要使用归纳才能证明的命题。
    上面的情形看起来似曾相识，但并不是巧合。这一次，解决方法仍然是使用……归纳！

    对证据和对数据使用 [induction] 具有同样的行为：它导致 Coq 对每个可用于构造证据的
    构造子生成一个子目标，同时对递归出现的问题性质提供了归纳假设。

    To prove a property of [n] holds for all numbers for which [even
    n] holds, we can use induction on [even n]. This requires us to
    prove two things, corresponding to the two ways in which [even n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [even n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [even n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** 让我们再次尝试证明这个引理： *)

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       同时 IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** 这里我们看到 Coq 对 [E'] 产生了 [IH]，而 [E'] 是唯一递归出现的
    [even] 命题。 由于 [E'] 中涉及到 [n']，这个归纳假设是关于 [n'] 的，
    而非关于 [n] 或其他数字的。  *)

(** 关于偶数性质的第二个和第三个定义的等价关系如下： *)

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** 我们会在后面的章节中看到，对证据进行归纳在很多领域里是一种常用的技术，
    特别是在形式化程序语言的语义时，由于其中很多有趣的性质都是归纳定义的。 *)

(** 下面的练习提供了一些简单的例子，来帮助你熟悉这项技术。 *)

(** **** 练习：2 星, standard (ev_sum)  *)
Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced, optional (even'_ev)  

    一般来说，有很多种方式来归纳地定义一个性质。比如说，下面是关于
    [even] 的另一种（蹩脚的）定义：*)

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

(** 请证明这个定义在逻辑上等同于前述定义。（当进入到归纳步骤时，你可能会想参考一下上一个定理。）*)

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced, recommended (ev_ev__ev)  

    在本题中找到适合进行归纳的项需要一点技巧： *)

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (ev_plus_plus)  

    这个练习仅仅需要使用前述引理，而不需要使用归纳或分类讨论，尽管一些重写可能会比较乏味。 *)

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 归纳关系 *)

(** 我们可以认为被一个数所参数化的命题（比如 [even]）是一个_'性质'_，也即，
    它定义了 [nat]　的一个子集，其中的数可以被证明满足此命题。
    以同样的方式，我们可认为有两个参数的命题是一个_'关系'_，也即，它定义了一个
    可满足此命题的序对集合。*)

Module Playground.

(** 一个很有用的例子是整数的“小于等于”关系。*)

(** 下面的定义应当是比较直观的。它提供了两种方法来描述一个数小于等于另一个数的证据：
    要么可观察到两个数相等，或提供证据显示第一个数小于等于第二个数的前继。　*)

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** 类似于证明 [even] 这样的性质，使用 [le_n] 和 [le_S] 构造子来证明关于 [<=]
    的事实遵循了同样的模式。我们可以对构造子使用 [apply] 策略来证明 [<=] 目标
    （比如证明 [3<=3] 或 [3<=6]），也可以使用 [inversion] 策略来从上下文中 [<=]
    的假设里抽取信息（比如证明 [(2<=1) -> 2+2=5]）。 *)

(** 这里提供一些完备性检查。（请注意，尽管这同我们在开始课程时编写的
    函数“单元测试”类似，但我们在这里必须明确地写下他们的证明——[simpl] 和
    [reflexivity] 并不会有效果，因为这些证明不仅仅是对表达式进行简化。）  *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* 课上已完成 *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* 课上已完成 *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* 课上已完成 *)
  intros H. inversion H. inversion H2.  Qed.

(** 现在“严格小于”关系 [n < m] 可以使用 [le] 来定义。 *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** 这里展示了一些定义于自然数上的关系：*)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

(** **** 练习：2 星, standard, optional (total_relation)  

    请定一个二元归纳关系 [total_relation] 对每一个自然数的序对成立。 *)

(* 请在此处解答 

    [] *)

(** **** 练习：2 星, standard, optional (empty_relation)  

    请定一个二元归纳关系 [empty_relation] 对自然数永远为假。 *)

(* 请在此处解答 

    [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** 练习：3 星, standard, optional (le_exercises)  

    这里展示一些 [<=] 和 [<] 关系的事实，我们在接下来的课程中将会用到他们。
    证明他们将会是非常有益的练习。 *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 (* 请在此处解答 *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  (* 请在此处解答 *) Admitted.

(** 提示：在下面的问题中，对 [m] 进行归纳会使证明容易一些。*)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** 提示：这个定理可以不通过使用 [induction] 来证明。*)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

Module R.

(** **** 练习：3 星, standard, recommended (R_provability)  

    通过同样的方式，我们可以定义三元关系、四元关系等。例如，考虑以下定义在自然数上的三元关系： *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - 下列哪个命题是可以被证明的？
      - [R 1 1 2]
      - [R 2 2 6]

    - 如果在 [R] 的定义中我们丢弃 [c5] 构造子，可被证明的集合会发生变化吗？
      简要（一句话）解释你的答案。

    - 如果在 [R] 的定义中我们丢弃 [c4] 构造子，可被证明的集合会发生变化吗？
      简要（一句话）解释你的答案。

(* 请在此处解答 *)
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, standard, optional (R_fact)  

    关系 [R] 其实编码了一个熟悉的函数。请找出这个函数，定义它并在 Coq 中证明他们等价。*)

Definition fR : nat -> nat -> nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

End R.

(** **** 练习：2 星, advanced (subsequence)  

    如果一个列表的所有元素以相同的顺序出现在另一个列表之中（但允许其中出现其他额外的元素），
    我们把第一个列表称作第二个列表的_'子序列'_。 例如：

      [1;2;3]

    是以下所有列表的子序列

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    但_'不是'_以下列表的子序列

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - 在 [list nat] 上定一个归纳命题 [subseq]，其表达了子序列的涵义。
      （提示：你需要三个分类。）

    - 证明子序列的自反关系 [subseq_refl]，也即任何列表是它自身的子序列。

    - 证明关系 [subseq_app] 对任意列表 [l1]，[l2] 和 [l3]，如果 [l1] 是 [l2]
      的子序列，那么 [l1] 也是 [l2 ++ l3] 的子序列。

    - （可选的，困难）证明子序列的传递关系 [subseq_trans]——也即，如果 [l1] 是 [l2]
      的子序列，且 [l2] 是 [l3] 的子序列，那么 [l1] 是 [l3] 的子序列。
      （提示：仔细选择进行归纳的项！） *)

Inductive subseq : list nat -> list nat -> Prop :=
(* 请在此处解答 *)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* 请在此处解答 *) Admitted.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (R_provability2)  

    假设我们在 Coq 中有如下定义：

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    下列命题哪个是可被证明的？

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* 请在此处解答 

    [] *)

(* ################################################################# *)
(** * 案例学习：正则表达式 *)

(** 性质 [even] 提供了一个简单的例子来展示归纳定义和其基础的推理技巧，
    但这还不是什么激动人心的东西——毕竟，[even] 等价于我们之前见过的两个非归纳的定义，
    而看起来归纳定义并没有提供什么好处。为了更好地展示归纳定义的表达能力，
    我们继续使用它来建模计算机科学中的一个经典概念——正则表达式。 *)

(** 正则表达式是用来描述字符串集合的一种简单语言，定义如下： *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

(** 请注意这个定义是_'多态的'_：[reg_exp T] 中的正则表达式描述了字符串，
    而其中的字符取自 [T]——也即，[T] 的元素构成的列表。

    （同一般的实践略有不同，我们不要求类型 [T] 是有限的。由此可形成一些不同的正则表达式
    理论，但对于我们在本章的目的而言并无不同。） *)

(** 我们通过以下规则来构建正则表达式和字符串，这些规则定义了正则表达式何时匹配一个字符串：

      - 表达式 [EmptySet] 不匹配任何字符串。

      - 表达式 [EmptyStr] 匹配空字符串 [[]].

      - 表达式 [Char x] 匹配单个字符构成的字符串 [[x]].

      - 如果 [re1] 匹配 [s1], 且 [re2] 匹配 [s2], 那么 [App re1 re2] 匹配 [s1 ++ s2].

      - 如果 [re1] 和 [re2] 中至少一个匹配 [s], 那么 [Union re1 re2] 匹配 [s].

      - 最后，如果我们写下某个字符串 [s] 作为一个字符串序列的连接
        [s = s_1 ++ ... ++ s_k]，且表达式 [re] 匹配其中每一个字符串 [s_i]，那么
        [Star re] 匹配 [s]。

        作为特殊情况，此字符串序列可能为空，因此无论 [re] 是什么 [Star re] 总是匹配空字符串 [[]]。*)

(** 容易把非形式化的定义翻译为使用 [Inductive] 的定义：*)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

(** 出于可读性的考虑，在此我们也展示使用推断规则表示的定义。
    于此同时，我们引入可读性更好的中缀表示法。*)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** 请注意这些规则不_'完全'_等同于之前给出的非形式化定义。
    首先，我们并不需要一个规则来直接表述无字符串匹配 [EmptySet]；
    我们做的仅仅是不囊括任何可能导致有字符串被 [EmptySet] 所匹配的规则。
    （的确，归纳定义的语法并不_'允许'_我们表达类似的“否定规则”（negative rule））。

    其次，非形式化定义中的 [Union] 和 [Star] 各自对应了两个构造子：
    [MUnionL] / [MUnionR]，和 [MStar0] / [MStarApp]。这在逻辑上等价于
    原始的定义，但在 Coq 中这样更加方便，因为递归出现的 [exp_match]
    是作为构造子的直接参数给定的，这在对证据进行归纳时更简单。
    （练习 [exp_match_ex1] 和 [exp_match_ex2] 会要求你证明归纳定义中的构造子
    和从非形式化规则的表述中提炼的规则确实是等价的。）

    接下来我们对一些例子使用这些规则： *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** （请注意，后一个例子对字符串 [[1]] 和 [[2]] 直接应用了 [MApp]。
    由于目标的形式是 [[1; 2]] 而非 [[1] ++ [2]]，Coq 并不知道如何分解这个字符串。）

    使用 [inversion]，我们还可以证明某些字符串_'不'_匹配一个正则表达式： *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** 我们可以定义一些辅助函数来简化正则表达式的书写。函数 [reg_exp_of_list]
    接受一个列表做参数，并构造一个正则表达式来精确地匹配这个列表：*)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** 我们还可以证明一些关于 [exp_match] 的性质。比如，下面的引理显示
    任意一个匹配 [re] 的字符串 [s] 也匹配 [Star re]。 *)

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** （请注意对 [app_nil_r] 的使用改变了目标，以此可匹配 [MStarApp] 所需要的形式。）*)

(** **** 练习：3 星, standard (exp_match_ex1)  

    下面的引理显示从形式化的归纳定义中可以得到本章开始的非形式化匹配规则。 *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* 请在此处解答 *) Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* 请在此处解答 *) Admitted.

(** 接下来的引理使用了 [Poly] 一章中出现的 [fold] 函数：
    如果 [ss : list (list T)] 表示一个字符串序列 [s1, ..., sn]，那么
    [fold app ss []] 是将所有字符串连接的结果。*)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard, optional (reg_exp_of_list_spec)  

    请证明 [reg_exp_of_list] 满足以下规范： *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 由于 [exp_match] 以递归方式定义，我们可能会发现
    关于正则表达式的证明常常需要对证据进行归纳。*)

(** 比如，假设我们想要证明以下显然的结果：如果正则表达式 [re] 匹配某个字符串 [s]，
    那么 [s] 中的所有元素必在 [re] 中某处以字符字面量的形式出现。

    为了表达这个定理，我们首先定义函数 [re_chars] 来列举一个正则表达式中出现的
    所有字符：*)

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** 接下来我们这样陈述此定理： *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* 课上已完成 *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** 特别关注一下对 [MStarApp] 分类的证明。我们得到了_'两个'_归纳假设：
    一个适用于 [x] 出现在 [s1] 中（当匹配 [re] 时），另一个则适用于
    [x] 出现在 [s2] 中（当匹配 [Star re] 时）。
    这是一个很好的例子来表明为什么我们需要对 [exp_match] 的证据而非 [re]
    进行归纳：对后者的归纳仅仅提供匹配 [re] 的字符串的归纳假设，却无法允许我们对
    [In x s2] 分类进行推理。 *)

  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** 练习：4 星, standard (re_not_empty)  

    请编写一个递归函数 [re_not_empty] 用来测试某个正则表达式是否会匹配一些字符串。
    并证明你的函数是正确的。*)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** [remember] 策略 *)

(** [induction] 策略让人困惑的一个特点是它会接受任意一个项并尝试归纳，
    即使这个项不够一般（general）。其副作用是会丢失掉一些信息（类似没有 [eqn:]
    从句的 [destruct]），并且使你无法完成证明。比如： *)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** 仅仅对 [H1] 反演并不会对处理含有递归的分类有太多帮助。（尝试一下！）
    因此我们需要对证据进行归纳！下面是一个朴素的尝试：*)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** 现在，尽管我们得到了七个分类（正由我们从 [exp_match] 的定义中期待的那样），
    但 [H1] 还是丢失了一个非常重要的信息：[s1] 事实上匹配了某种形式的 [Star re]。
    这意味着对于_'全部'_的七个构造子分类我们都需要给出证明，尽管其中两个（[MStar0]
    和 [MStarApp]）是自相矛盾的。
    我们仍然可以在一些构造子上继续证明，比如 [MEmpty]…… *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ……但有一些分类我们却卡住了。比如，对于 [MChar] 我们需要证明

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    这显然是不可能完成的。 *)

  - (* MChar. 卡住了…… *)
Abort.

(** 问题是，只有当 [Prop] 的假设是完全一般的时候，对其使用 [induction] 的才会起作用，
    也即，我们需要其所有的参数都是变量，而非更复杂的表达式，比如 [Star re]。

    （由此，对证据使用 [induction] 的行为更像是没有 [eqn:] 的 [destruct]
    而非 [inversion]。）

    解决此问题的一种直接的方式是“手动推广”这个有问题的表达式，
    即为此引理添加一个显式的等式： *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** 我们现在可以直接对证据进行归纳，因为第一个假设的参数已经足够一般，
    这意味着我们可以通过反演当前上下文中的 [re' = Star re] 来消解掉多数分类。

    这在 Coq 中是一种常用的技巧，因此 Coq 提供了策略来自动生成这种等式，
    并且我们也不必改写定理的陈述。*)

Abort.

(** 在 Coq 中调用 [remember e as x] 策略会（1）替换所有表达式 [e] 为变量 [x]，
    （2）在当前上下文中添加一个等式 [x = e]。我们可以这样使用 [remember]
    来证明上面的结果： *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** 我们现在有 [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(**  [Heqre'] 与多数分类相互矛盾，因此我们可以直接结束这些分类。*)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** 值得注意的分类是 [Star]。请注意 [MStarApp] 分类的归纳假设 [IH2]
    包含到一个额外的前提 [Star re'' = Star re']，这是由 [remember]
    所添加的等式所产生的。*)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(** **** 练习：4 星, standard, optional (exp_match_ex2)  *)

(** 下面的引理 [MStar'']（以及它的逆，之前的练习题中的 [MStar']）显示
    [exp_match] 中 [Star] 的定义等价于前面给出的非形式化定义。*)

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, advanced (pumping)  

    正则表达式中一个非常有趣的定理叫做_'泵引理（Pumping Lemma）'_，
    非形式化地来讲，它陈述了任意某个足够长的字符串 [s] 若匹配一个正则表达式 [re]，
    则可以被抽取（pumped）——将 [s] 的某个中间部分重复任意次产生的新字符串
    仍然匹配 [re]。

    我们首先定义什么是“足够长”。由于 Coq 中使用的是构造性逻辑，我们事实上需要计算
    对于任何一个正则表达式 [re] 其最小的“可被抽取（pumpability）”长度。*)

Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** 接下来，定义辅助函数 [napp] 来重复（连接到它自己）一个字符串特定次数。*)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** 现在，泵引理是说，如果 [s =~ re] 且 [s] 的长度最小是 [re] 的抽取常数（pumping constant），
    那么 [s] 可分割成三个子字符串 [s1 ++ s2 ++ s3]，其中 [s2] 可被重复任意次，
    其结果同 [s1] 和 [s3] 合并后仍然匹配 [re]。由于 [s2] 必须为非空字符串，
    这是一种（构造性的）方式来以我们想要的长度生成匹配 [re] 的字符串。 *)

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** 为了简化证明（也就是接下来你需要填写的），我们使用 [Require] 来引入 [omega] 策略，
    其可用于自动化地完成一些自然数等式和不等式的枯燥证明。
    我们在后面的章节中会详细解释 [omega]，不过在这里请尝试做一些实验。
    下面的第一个归纳分类中展示了如何使用它。 *)

Import Coq.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  (* 请在此处解答 *) Admitted.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * 案例学习：改进互映 *)

(** 在 [Logic] 一章中，我们经常需要关联起对布尔值的计算和 [Prop]
    中的陈述，然而进行这样的关联往往会导致冗长的证明。请考虑以下定理的证明：*)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** 在 [destruct] 后的第一个分支中，我们解构 [n =? m]
    后生成的等式显式地使用了 [eqb_eq] 引理，以此将假设
    [n =? m] 转换为假设 [n = m]；接着使用 [rewrite]
    策略和这个假设来完成此分支的证明。*)

(** 为了简化这样的证明，我们可定义一个归纳命题，用于对 [n =? m]
    产生更好的分类讨论原理。
    它不会生成类似 [(n =? m) = true]这样的等式，因为一般来说对证明并不直接有用，
    其生成的分类讨论原理正是我们所需要的假设: [n = m]。*)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** 性质 [reflect] 接受两个参数：一个命题 [P] 和一个布尔值 [b]。
    直观地讲，它陈述了性质 [P] 在布尔值 [b] 中所_'映现'_（也即，等价）：
    换句话说，[P] 成立当且仅当 [b = true]。为了理解这一点，请注意定义，
    我们能够产生 [reflect P true] 的证据的唯一方式是证明 [P] 为真并使用
    [ReflectT] 构造子。如果我们反转这个陈述，意味着从 [reflect P true]
    的证明中抽取出 [P] 的证据也是可能的。与此类似，证明 [reflect P false]
    的唯一方式是合并 [~ P] 的证据和 [ReflectF] 构造子。

    形式化这种直觉并证明 [P <-> b = true] 和 [reflect P b]
    这两个表述确实等价是十分容易的。首先是从左到右的蕴含：*)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* 课上已完成 *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** 练习：2 星, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 使用 [reflect] 而非“当且仅当”连词的好处是，通过解构一个形如
    [reflect P b] 的假设或引理，我们可以对 [b]
    进行分类讨论，同时为两个分支（第一个子目标中的 [P]
    和第二个中的 [~ P]）生成适当的假设。 *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** [filter_not_empty_In] 的一种更流畅证明如下所示。请注意对 [destruct] 和 [apply]
    的使用是如何合并成一个 [destruct] 的使用。 *)

(** （为了更清晰地看到这点，使用 Coq 查看 [filter_not_empty_In]
    的两个证明，并观察在 [destruct] 的第一个分类开始时证明状态的区别。） *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** 练习：3 星, standard, recommended (eqbP_practice)  

    使用上面的 [eqbP] 证明以下定理：*)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 这个小例子展示了互映证明可以怎样为我们提供一些便利。在大型的开发中，
    使用 [reflect] 往往更容易写出清晰和简短的证明脚本。我们将会在后面的章节
    和_'编程语言基础'_一卷中看到更多的例子。

    对 [reflect] 性质的使用已被 _'SSReflect'_ 推广开来，这是一个
    Coq 程序库，用于形式化一些数学上的重要结果，包括四色定理和法伊特－汤普森定理。
    SSReflect 的名字代表着 _'small-scale reflection'_，也即，普遍性地使用
    互映来简化与布尔值计算有关的证明。*)

(* ################################################################# *)
(** * 额外练习 *)

(** **** 练习：3 星, standard, recommended (nostutter_defn)  

    写出性质的归纳定义是本课程中你需要的重要技能。请尝试去独立解决以下的练习。

    列表连续地重复某元素称为 "百叶窗式" (stutter)。
    （此概念不同于不包含重复元素：[1;4;1] 虽然包含重复元素 [1]，
    但因其未连续出现，故不是百叶窗式列表）。
    [nostutter mylist] 表示 [mylist] 不是百叶窗式列表。
    请写出 [nostutter] 的归纳定义。 *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* 请在此处解答 *)
.
(** 请确保以下测试成功，但如果你觉得我们建议的证明（在注释中）并不有效，也可随意更改他们。
    若你的定义与我们的不同，也可能仍然是正确的，但在这种情况下可能需要不同的证明。
    （你会注意到建议的证明中使用了一些我们尚未讨论过的策略，这可以让证明适用于不同的 [nostutter]
    定义方式。你可以取消注释并直接使用他们，也可以用基础的策略证明这些例子。） *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* 请在此处解答 *) Admitted.
(* 
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* 请在此处解答 *) Admitted.
(* 
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* 请在此处解答 *) Admitted.
(* 
  Proof. repeat constructor; apply eqb_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* 请在此处解答 *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction Hneq0; auto. Qed.
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** 练习：4 星, advanced (filter_challenge)  

    让我们证明在 [Poly] 一章中 [filter] 的定义匹配某个抽象的规范。
    可以这样非形式化地描述这个规范：

    列表 [l] 是一个 [l1] 和 [l2] 的“顺序合并”（in-order merge），如果它以
    [l1] 和 [l2] 中元素的顺序包含 [l1] 和 [l2] 中的所有元素，尽管可能是交替的。比如：

    [1;4;6;2;3]

    是

    [1;6;2]

    和

    [4;3].

    的顺序合并。

    现在，假设我们有集合 [X]，函数 [test: X->bool] 和一个类型为 [list X] 的列表
    [l]。接着接设如果 [l] 是 [l1] 和 [l2] 的顺序合并，且 [l1] 中的每个元素满足 [test]，
    而 [l2] 中没有元素满足 [test]，那么 [filter test l = l1]。

    请将这段规范翻译为 Coq 中的定理并证明它。（你首先需要定义合并两个列表的含义是什么。
    请使用归纳关系而非 [Fixpoint] 来完成。）*)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, advanced, optional (filter_challenge_2)  

    另一种刻画 [filter] 行为的方式是：在 [l] 的所有其元素满足 [test] 的子序列中，
    [filter test l] 是最长的那个。请形式化这个命题并证明它。*)

(* 请在此处解答 

    [] *)

(** **** 练习：4 星, standard, optional (palindromes)  

    回文是倒序排列与正序排列相同的序列。

    - 在 [listX] 上定义一个归纳命题 [pal] 来表达回文的含义。
      （提示：你需要三个分类。定义应当基于列表的结构；仅仅使用一个构造子，例如

        c : forall l, l = rev l -> pal l

      看起来十分显而易见，但并不会很好的工作。)

    - 证明（[pal_app_rev]）

       forall l, pal (l ++ rev l).

    - 证明（[pal_rev] that）

       forall l, pal l -> l = rev l.
*)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, standard, optional (palindrome_converse)  

    由于缺乏证据，反方向的证明要困难许多。使用之前练习中定义的 [pal] 来证明

     forall l, l = rev l -> pal l.
*)

(* 请在此处解答 

    [] *)

(** **** 练习：4 星, advanced, optional (NoDup)  

    请回忆一下 [Logic] 章节中性质 [In] 的定义，其断言值 [x] 在列表 [l] 中至少出现一次：*)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** 你的第一个任务是使用 [In] 来定义命题 [disjoint X l1 l2]：仅当列表 [l1]
    和 [l2]（元素的类型为 [X]）不含有相同的元素时其可被证明。*)

(* 请在此处解答 *)

(** 接下来，使用 [In]　定义归纳命题 [NoDup X l]，其可被证明仅当列表 [l]
    （元素类型为 [X]）的每个元素都不相同。比如，[NoDup nat [1;2;3;4]]
    和 [NoDup bool []] 是可被证明的，然而 [NoDup nat [1;2;1]]
    和 [NoDup bool [true;true]] 是不行的。*)

(* 请在此处解答 *)

(** 最后，使用 [disjoint]，[NoDup] 和 [++]（列表连接）陈述并证明一个或多个有趣的定理。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** 练习：4 星, advanced, optional (pigeonhole_principle)  

    _鸽笼原理（Pigeonhole Principle）'_是一个关于计数的基本事实：
    将超过 [n] 个物体放进 [n] 个鸽笼，则必有鸽笼包含至少两个物体。
    与此前诸多情形相似，这一数学事实看似乏味，但其证明手段并不平凡，
    如下所述： *)

(** 首先容易证明一个有用的引理。 *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* 请在此处解答 *) Admitted.

(** 现在请定一个性质 [repeats]，使 [repeats X l] 断言 [l]
    包含至少一个（类型为 [X] 的）重复的元素。*)

Inductive repeats {X:Type} : list X -> Prop :=
  (* 请在此处解答 *)
.

(** 现在，我们这样来形式化鸽笼原理。假设列表 [l2] 表示鸽笼标签的列表，列表 [l1]
    表示标签被指定给一个列表里的元素。如果元素的个数多于标签的个数，那么至少有两个
    元素被指定了同一个标签——也即，列表 [l1] 含有重复元素。

    如果使用 [excluded_middule] 假设并展示 [In] 是可判定的（decidable），
    即 [forall x l, (In x l) \/ ~ (In x l)]，那么这个证明会容易很多。
    然而，若_'不'_假设 [In] 的可判定性也同样可以证明它；在这样的情况下便不必使用
    [excluded_middle] 假设。 *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 扩展练习：经验证的正则表达式匹配器 *)

(** 我们现在已经定义了正则表达式的匹配关系和多态列表。我们可以使用这些定义来手动地证明
    给定的正则表达式是否匹配某个字符串，但这并不是一个可以自动地判断是否匹配的程序。

    有理由期待，用于构造匹配关系证据的归纳规则可以被翻译为一个递归函数，
    其在正则表达式上的递归对应于这种关系。然而，定义这样的函数并没有那么直接，
    由于给定的正则表达式会被 Coq 识别为递归变量，作为结果，Coq 并不会接受这个函数，
    即使它总是停机。

    重度优化的匹配器会将正则表达式翻译为一个状态机，并决定状态机是否接受
    某个字符串。然而，正则表达式匹配也可以通过一个算法来实现，其仅仅操作字符串和
    正则表达式，无需定义和维护额外的数据类型，例如状态机。我们将会实现这样的算法，
    并验证其值与匹配关系是互映的。 *)

(** 我们将要实现的正则表达式匹配器会匹配由 ASCII 字符构成的列表：*)
Require Export Coq.Strings.Ascii.

Definition string := list ascii.

(** Coq 标准库中包含了一个不同的 ASCII 字符串的归纳定义。然而，为了应用
    之前定义的匹配关系，我们在此使用刚刚给出的 ASCII 字符列表作为定义。

    我们也可以定义工作在多态列表上的正则表达式匹配器，而非特定于 ASCII 字符列表。
    我们将要实现的匹配算法需要知道如何对列表中的元素判断相等，因此需要给定一个
    相等关系测试函数。一般化我们给出的定义、定理和证明有一点枯燥，但是可行的。 *)

(** 正则表达式匹配器的正确性证明会由匹配函数的性质和 [match] 关系的性质组成，
    [match] 关系并不依赖匹配函数。我们将会首先证明后一类性质。他们中的多数
    将会是很直接的证明，已经被直接给出；少部分关键的引理会留给你来证明。 *)

(** 每个可被证明的 [Prop] 等价于 [True]。 *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** 其逆可被证明的 [Prop] 等价于 [False]。 *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] 不匹配字符串。 *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] 仅匹配空字符串。 *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] 不匹配非空字符串。 *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] 不匹配不以 [a] 字符开始的字符串。 *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** 如果 [Char a] 匹配一个非空字符串，那么这个字符串的尾（tail）为空。 *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] 匹配字符串 [s] 当且仅当 [s = s0 ++ s1]，其中 [s0]
    匹配 [re0] 且 [s1] 匹配 [re1]。 *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** 练习：3 星, standard, optional (app_ne)  

    [App re0 re1] 匹配 [a::s] 当且仅当 [re0] 匹配空字符串
    且 [a::s] 匹配 [re1] 或 [s=s0++s1]，其中 [a::s0] 匹配 [re0]
    且 [s1] 匹配 [re1]。

    尽管这个性质由纯粹的匹配关系构成，它是隐藏在匹配器的设计背后的一个重要观察。
    因此（1）花一些时间理解它，（2）证明它，并且（3）留心后面你会如何使用它。*)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** [s] 匹配 [Union re0 re1] 当且仅当 [s] 匹配 [re0] 或 [s] 匹配 [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** 练习：3 星, standard, optional (star_ne)  

    [a::s] 匹配 [Star re] 当且仅当 [s = s0 ++ s1]，其中 [a::s0] 匹配
    [re] 且 [s1] 匹配 [Star re]。 同 [app_ne]一样，这个观察很重要，
    因此理解，证明并留意它。

    提示：你需要进行归纳。的确是有几个合理的候选 [Prop] 来进行归纳。
    但唯一其作用的方式是首先拆分 [iff] 为两个蕴含式，然后在 [a :: s =~ Star re]
    的证据上进行归纳来证明其中一个。另一个蕴含式可以无需使用归纳来证明。

    为了在正确的性质上归纳，你需要使用 [remember] 策略来重新表述 [a :: s =~ Star re]，
    使其成为一般变量上的 [Prop]。 *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 我们的正则表达式匹配器定义包括两个不动点函数。第一个函数对给定的正则表达式 [re]
    进行求值，结果映射了 [re] 是否匹配空字符串。这个函数满足以下性质： *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** 练习：2 星, standard, optional (match_eps)  

    完成 [match_eps] 的定义，其测试给定的正则表达式是否匹配空字符串： *)
Fixpoint match_eps (re: @reg_exp ascii) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (match_eps_refl)  

    现在，请证明 [match_eps] 确实测试了给定的正则表达式是否匹配空字符串。
    （提示：你会使用到互映引理 [ReflectT] 和 [ReflectF]。） *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 我们将会定义其他函数也使用到 [match_eps]。然而，这些函数的证明中你唯一会用到的
    [match_eps] 的性质是 [match_eps_refl]。*)

(** 我们匹配器所进行的关键操作是迭代地构造一个正则表达式生成式的序列。
    对于字符 [a] 和正则表达式 [re]，[re] 在 [a] 上的生成式是一个正则表达式，
    其匹配所有匹配 [re] 且以 [a] 开始的字符串的后缀。也即，[re']
    是 [re] 在 [a] 上的一个生成式如果他们满足以下关系：*)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** 函数 [d] 生成字符串如果对于给定的字符 [a] 和正则表达式 [re]，
    它求值为 [re] 在 [a] 上的生成式。也即，[d] 满足以下关系： *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** 练习：3 星, standard, optional (derive)  

    请定义 [derive] 使其生成字符串。一个自然的实现是在某些分类使用
    [match_eps] 来判断正则表达式是否匹配空字符串。 *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(** [derive] 函数应当通过以下测试。每个测试都在将被匹配器所求值的表达式和
    最终被匹配器返回的结果之间确立一种相等关系。
    每个测试也被添加了它所反映的匹配事实的注解。*)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* 请在此处解答 *) Admitted.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* 请在此处解答 *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* 请在此处解答 *) Admitted.

(** **** 练习：4 星, standard, optional (derive_corr)  

    请证明 [derive] 确实总是会生成字符串。

    提示：一种证明方法是对 [re] 归纳，尽管你需要通过归纳和一般化合适的项来
    仔细选择要证明的性质。

    提示：如果你定义的 [derive] 对某个正则表达式 [re] 使用了 [match_eps]，
    那么可对 [re] 应用 [match_eps_refl]，接着对结果解构并生成
    分类，其中你可以假设 [re] 匹配或不匹配空字符串。

    提示：通过使用之前证明过的引理可以帮助一点你的工作。特别是，在证明归纳的
    许多分类时，通过之前的引理，你可以用一个复杂的正则表达式（比如，
    [s =~ Union re0 re1]）来重写命题，得到一个简单正则表达式上的命
    题构成的布尔表达式（比如，[s =~ re0 \/ s =~ re1]）。
    你可以使用 [intro] 和 [destruct] 来对这些命题进行推理。*)
Lemma derive_corr : derives derive.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 我们将会使用 [derive] 来定义正则表达式匹配器。然而，在匹配器的性质的证明中你唯一会用到
    的 [derive] 的性质是 [derive_corr]。 *)

(** 函数 [m] 匹配正则表达式如果对给定的字符串 [s] 和正则表达式 [re]，
    它求值的结果映射了 [s] 是否被 [re] 匹配。也即，[m] 满足以下性质：*)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** 练习：2 星, standard, optional (regex_match)  

    完成 [regex_match] 的定义，使其可以匹配正则表达式。*)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (regex_refl)  

    最后，证明 [regex_match] 确实可以匹配正则表达式。

    提示：如果你定义的 [regex_match] 对正则表达式 [re] 使用了 [match_eps]，
    那么可对 [re] 应用 [match_eps_refl]，接着对结果解构并生成
    分类，其中你可以假设 [re] 匹配或不匹配空字符串。

    提示：如果你定义的 [regex_match] 对字符 [x] 和正则表达式 [re] 使用了 [derive]，
    那么可对 [x] 和 [re] 应用 [derive_corr]，以此证明 [x :: s =~ re] 当给定
    [s =~ derive x re] 时，反之亦然。 *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* Fri Jul 19 00:32:20 UTC 2019 *)
