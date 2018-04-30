(** * IndProp: 归纳定义的命题 *)

Set Warnings "-notation-overridden,-parsing".
Require Export Logic.
Require Coq.omega.Omega.

(* ################################################################# *)
(** * 归纳定义的命题 *)

(** 在 [Logic] 一章中，我们学习了多种方法来编写命题，包括合取、析取和量词。
    在本章中，我们引入新的方式：_'归纳定义的命题（Inductive Definitions）'_。 *)

(** 请回想一下我们已经学过的两种方法来表达数字 [n] 是偶数：
    (1) [evenb n = true]，以及 (2) [exists k, n = double k] 。
    然而另一种可能是通过如下规则来建立数字 [n] 的偶数性质：

       - 规则 [ev_0]:  数字 [0] 是偶数。
       - 规则 [ev_SS]: 如果 [n] 是偶数, 那么 [S (S n)] 是偶数。 *)

(** 为了理解这样的偶数性质定义如何工作，我们可想象如何证明 [4] 是偶数。
    根据规则 [ev_SS]，需要证明 [2] 是偶数。这时，只要证明 [0] 是偶数，
    我们可继续通过规则 [ev_SS] 确保它成立。而规则 [ev_0] 可直接证明 [0] 是偶数。 *)

(** 接下来的课程中，我们会看到很多类似方式定义的命题。
    在非形式化的讨论中，使用轻量化的记法有助于阅读和书写。
    _'推断规则（Inference Rules）'_ 是其中一种： *)
(**

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))
*)

(** 
    若将前文所述的规则重新排版成推断规则，我们可以这样阅读它，如果线上方的 
    _'前提（Premises）'_ 成立，那么线下方的 _'结论（Conclusion）'_ 成立。
    比如，规则 [ev_SS] 是如果 [n] 满足 [ev]，那么 [S (S n)] 也满足。
    如果一条规则在线上方没有前提，则结论直接成立。

    我们可以通过组合推断规则来展示证明。下面展示如何转译 [4] 是偶数的证明： *)
(**

                             ------  (ev_0)
                              ev 0
                             ------ (ev_SS)
                              ev 2
                             ------ (ev_SS)
                              ev 4
*)

(**
    为什么我们把这样的证明称之为「树」（而非其他，比如「栈」）？
    因为一般来说推断规则可以有多个前提。我们会在后面看到一些例子。 *)

(** 基于上述，可将偶数性质的定义翻译为Coq中使用 [Inductive] 声明的定义，
    声明中每一个构造子对应一个推断规则： *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(** 这个定义同之前其他 [Inductive] 的使用有一个重要的区别：
    它的结果并不是一个 [Type] ，而是一个将 [nat] 映射到 [Prop] 的函数
    —— 即关于数的性质。
    注意我们曾见过其他的归纳定义结果为函数，比如 [list] ，其类型是 [Type -> Type] 。
    值得注意的是，由于 [ev] 中出现在冒号 _'右侧'_ 的 [nat] 参数是 _'未命名'_ 的，
    这允许在不同的构造子类型中使用不同的值：
    [ev_0] 类型中的 [0] 以及 [ev_SS] 类型中的 [S (S n)]。

    相反， [list] 的定义以 _'全局方式'_ 命名了冒号 _'左侧'_ 的参数 [X] ，
    强迫 [nil] 和 [cons] 的结果为同一个类型（ [list X] ）。
    如果在定义 [ev] 时我们将 [nat] 置于冒号左侧，会得到如下错误： *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** (「Parameter」 是 Coq 中的一个术语来表示 [Inductive] 定义中冒号左侧的参数；
    「index」 则指冒号右侧的参数。) *)

(** 在 Coq 中，我们可以认为 [ev] 定义了一个性质 [ev : nat -> Prop]，其包括原始定理
    [ev_0 : ev 0] 和 [ev_SS : forall n, ev n -> ev (S (S n))]。  *)

(** 这些 「定理构造子」 等同于被证明过的定理。
    特别的，我们可以使用 Coq 中的 [apply] 策略和规则名称来证明某个
    数字的 [ev] 性质…… *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** …… 或使用函数应用的语法： *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** 我们同样可以对前提中使用到 [ev] 的定理进行证明。 *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** 更一般地，我们可以证明以任意数字乘2是偶数： *)

(** **** Exercise: 1 star (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 在证明中使用证据 *)

(** 除了 _'构造'_ 证据（evidence）来表示某个数字是偶数，我们还可以对这些证据进行 _'推理'_。
    
    使用 [Inductive] 声明来引入 [ev] 不仅仅表示在 Coq 中 [ev_0] 和 [ev_SS] 
    这样的构造子是合法的方式来构造偶数证明的证据，他们也是 _'仅有的'_ 方式 
    （对 [ev] 而言）。 *)

(** 换句话说，如果某人展示了对于 [ev n] 的证据 [E]，那么我们知道 [E] 
    必是二者其一：

      - [E] 是 [ev_0] （且 [n] is [O]）, 或
      - [E] 是 [ev_SS n' E'] （且 [n] 是 [S (S n')], [E'] 是
        [ev n'] 的证据）. *)

(** 这样的形式暗示着，我们可以像分析归纳定义的数据结构一样分析他们；
    特别的，对于这类证据使用 _'归纳'_ 和 _'分类讨论'_ 来进行论证也是可行的。
    让我们通过一些例子来看看在实践中这意味着什么。 *)

(* ================================================================= *)
(** ** 对证据进行反演 *)

(** 假设我们正在证明涉及数字 [n] 的某个性质，且给定 [ev n] 作为前提。
    我们已经知道对 [n] 使用 [inversion] 策略可对 [n = 0] 和 [n = S n']
    进行分类讨论，同时 [inversion] 会生成子目标。但对于一些证明，我们想
    _'直接'_ 对证据 [ev n] 进行分析：

    根据 [ev] 的定义，有两种情况需要考虑：

    - 如果证据形如 [ev_0]，那么可得 [n = 0]。

    - 否则，证据必然形如 [ev_SS n' E']，其中 [n = S (S n')] 且
      [E'] 是 [ev n'] 的证据。 *)

(** 在 Coq 中进行此类推理，我们也可以使用 [inversion] 策略。
    除了可对涉及到构造子的等式进行推理，[inversion] 对归纳定义的命题
    提供了分类讨论的原则。当以此种方式使用它时，语法与 [destruct] 类似：
    我们需提供一个由 [|] 分隔的标识符列表来命名构造子中的参数。 *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** 在这个证明中反演推理的工作方式如下：

    - 如果证据形如 [ev_0]，那么我们可得 [n = 0]。
      因此，需要证明 [ev (pred (pred 0))] 成立。
      根据 [pred] 的定义，这等同于证明 [ev 0]，即可从 [ev 0] 直接得证。

    - 否则，证据必然形如 [ev_SS n' E']，其中 [n = S (S n')] 且 [E'] 是
      [ev n'] 的证据。我们需要证明 [ev (pred (pred (S (S n'))))] 成立，
      在简化后，可从 [E'] 得证。 *)

(** 如果我们把 [inversion] 替换为 [destruct]，这个证明同样工作： *)

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** 将一个由归纳性质（inductive property）构成的假设作用于复杂的表达式
    （而非一个变量）时， 使用 [inversion] 会比 [destruct] 更加方便。
    这里有一个具体的例子。假设我们想要证明 [ev_minus2] 的变种： *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

(** 直观来说，我们知道支撑前提的证据不会由 [ev_0] 组成，因为 [0] 和 [S] 是
    [nat] 类型不同的构造子；由此 [ev_SS] 是唯一需要应对的情况（译注：[ev_0] 无条件成立）。
    不幸的是，[destruct] 并没有如此智能，它仍然为我们生成两个子目标。
    更甚至，于此同时最终目标没有改变，也无法为完成证明提供任何有用的信息。 *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* 我们须证明 [n] 是偶数，但没有任何有用的假设信息可以使用！ *)
Abort.

(** 究竟发生了什么？ 应用 [destruct] 把性质的参数替换为对应于构造子的值。
    这对于证明 [ev_minus2'] 是有帮助的，因为在最终目标中直接使用到了参数 [n]。
    然而，这对于 [evSS_ev] 并没有帮助，因为被替换掉的 [S (S n)] 并没有在其他地方被使用。*)

(** 另一方面，[inversion] 策略可以检测到（1）第一个分类是不适用的（译注：[ev_0]），
    以及（2）出现在 [ev_SS] 中的 [n'] 必等同于 [n]。
    这帮助我们完成了证明： *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** 通过 [inversion]，我们可以对「显然矛盾的」归纳性质假设应用爆炸原理（principle of explosion）。
    比如： *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star (SSSSev__even)  *)
(** 请使用 [inversion] 策略证明以下结果。 *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 1 star (even5_nonsense)  *)
(** 请使用 [inversion] 策略证明以下结果。 *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 初看我们使用 [inversion] 的方式似乎有点难以理解。 
    目前为止，我们只对相等性命题使用 [inversion]，以此来利用构造子的单射性
    或区分不同的构造子（TODO：injectivity翻译） 。
    但我们将要看到 [inversion] 也可以用于分析归纳定义命题的证据。
    
    一般来说 [inversion] 以这样的方式工作。设想在当前上下文中名称 [I] 指向
    假设 [P]，而[P] 由一个 [Inductive] 声明所定义。
    接下来，使用 [inversion I] 会对 [P] 中的每一个构造子生成子目标，
    其中 [I] 会被替换为在这个构造子中为了证明 [P] 所需要满足的精确条件。
    有些子目标是自相矛盾的，[inversion] 会直接抛弃这些子目标。
    而为了证明最初的目标，剩下的情形必须被证明。对于这些，[inversion] 会添加
    [P] 成立所需要的等式到证明的上下文中。（比如 [evSS_ev] 证明中的 [S (S n') = n]。） *)

(** 上面的 [ev_double] 练习展示了偶数性质的一种新记法，其被之前的两种记法所蕴含。
    （因为，由  [Logic] 一章中的 [even_bool_prop]，我们已经知道
    他们是互相等价的。）
    为了展示这三种方式的一致性，我们需要下面的引理： *)

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.
(* 课上已完成 *)

(** 我们可以尝试使用分类讨论或对 [n] 进行归纳。
    但由于 [ev] 在前提中出现，如同之前章节的一些例子，这种策略或许无法行得通。
    如此我们似乎可以首先尝试对 [ev] 的证据进行反演。
    确实，第一个分类可以被平凡地证明。 *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** 不幸地是，第二个分类要困难一些。我们需要证明 [exists k, S (S n') = double k]，
    但唯一可用的假设是 [E']，也即 [ev n'] 成立。由于这并不直接有用，
    我们似乎被卡住了，而对 [E] 进行分类讨论是徒劳的。

    如果仔细观察第二个（子）目标，我们可以看到一些有意思的事情：
    对 [E] 进行分类讨论，我们可以把要证明的原始结果归约到另一个上，
    其涉及到一个不同 [ev] 的证据： [E']。
    形式化地说，我们可以完成证明通过展示：


        exists k', n' = double k',

    
    这同原始的命题是一致的，只是 [n'] 被替换为 n。确实，通过这个中间结果完成证明
    并不困难。  *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* 将原始目标归约到新目标上 *)

Admitted.

(* ================================================================= *)
(** ** 对证据进行归纳 *)

(** 看起来很类似，但这并不是巧合：我们遇到了类似 [Induction] 章节中的问题，
    对于需要使用归纳来证明的命题我们使用了分类讨论。
    再一次地，解决方法是使用……归纳！

    对证据和对数据使用 [induction] 的行为是相同的：它导致 Coq 对每个可用于构造证据的
    构造子生成一个子目标，同时对递归出现的问题命题提供了归纳假设。 *)

(** 让我们再次尝试证明这个引理： *)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
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
    [ev] 命题。 由于 [E'] 中涉及到 [n']，这个归纳假设是关于 [n'] 的，
    而非关于 [n] 或其他数字的。  *)

(** 关于偶数性质的第二个和第三个定义的等价性如下： *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** 我们会在后面的章节中看到，对证据进行归纳在很多领域里是一种常用的技术，
    特别是在形式化程序语言的语义时，由于其中很多有趣的性质都是归纳定义的。 *)

(** 下面的练习提供了一些简单的例子，来帮助你熟悉这项技术。 *)

(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)  *)
(** 一般来说，有很多种方式来归纳地定义一个性质。比如说，下面是关于 [ev] 的另一种（蹩脚的）定义：*)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(** 请证明这个定义在逻辑上等同于前述定义。（当进入到归纳环节时，你可能会想参考一下上一个定理。）*)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  *)
(** 在本题中找到合适的项进行归纳需要一点技巧： *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** 这个练习仅仅需要使用前述引理。不需要使用归纳和分类讨论，尽管一些重写可能会比较乏味。 *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 归纳关系 *)

(** 我们可以认为由数字参数化的命题（比如 [ev]）是一个_'性质'_，也即，
    它定义了 [nat]　的一个子集，其中的数字可以被证明满足此命题。
    以同样的方式，我们可认为有两个参数的命题是一个_'关系'_，也即，它定义了一个
    序对的集合可满足此命题。*)

Module Playground.

(** 一个很有用的例子是数字的「小于等于」关系。*)

(**　下面的定义应当是比较直观的。它提供了两种方法来描述一个数字小于等于另一个数字的证据：
    要么可观察到两个数字相等，或提供证据显示第一个数字小于等于第二个数字的前继。　*)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** 类似于证明 [ev] 这样的性质，使用 [le_n] 和 [le_S]　构造子来证明关于 [<=]
    的事实遵循了同样的模式。我们可以对构造子使用 [apply] 策略来证明 [<=] 目标
    （比如证明 [3<=3] 或 [3<=6]），也可以使用 [inversion] 策略来从上下文中 [<=] 的
    假设里抽取信息（比如证明 [(2<=1) -> 2+2=5]）。 *)

(** 这里提供一些完备性检查。（请注意，尽管这同我们在开始课程时编写的
    函数「单元测试」类似，但我们在这里必须明确地写下他们的证明—— [simpl] 和
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

(** 现在「严格小于」关系 [n < m] 可以使用 [le] 来定义。 *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** 这里展示了一些定义于数字上的关系：*)

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, optional (total_relation)  *)
(** 请定一个二元归纳关系 [total_relation] 对每一个自然数序对成立。 *)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 2 stars, optional (empty_relation)  *)
(** 请定一个二元归纳关系 [empty_relation] 对自然数永远为假。 *)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 3 stars, optional (le_exercises)  *)
(** 这里展示一些关于 [<=] 和 [<] 关系的事实，我们在接下来的课程中将会用到他们。
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
  leb n m = true -> n <= m.
Proof.
  (* 请在此处解答 *) Admitted.

(** 提示：在下面的问题中，对 [m] 进行归纳会使证明容易一些。*)

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  (* 请在此处解答 *) Admitted.

(** 提示：这个定理可以不通过使用 [induction] 来证明。*)

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

Module R.

(** **** Exercise: 3 stars, recommended (R_provability)  *)
(** 通过同样的方式，我们可以定义三元关系、四元关系等。例如，考虑以下定义在数字上的三元关系： *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - 下列哪个命题是可以被证明的？
      - [R 1 1 2]
      - [R 2 2 6]

    - 如果在 [R] 的定义中我们丢弃 [c5] 构造子，可被证明的集合会发生变化吗？
      简要（一句话）解释你的答案。

    - 如果在 [R] 的定义中我们丢弃 [c4] 构造子，可被证明的集合会发生变化吗？
      简要（一句话）解释你的答案。

(* 请在此处解答 *)
*)
(** [] *)

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** 关系 [R] 其实编码了一个熟悉的函数。请找出这个函数，定义它并在 Coq 中证明他们等价。*)

Definition fR : nat -> nat -> nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** 如果一个列表的所有元素以相同的顺序出现在另一个列表之中（但允许其中出现其他额外的元素），
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

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability2)  *)
(** 假设我们在 Coq 中有如下定义：

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    下列命题哪个是可被证明的？

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(** [] *)


(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for illustrating
    inductive definitions and the basic techniques for reasoning about
    them, but it is not terribly exciting -- after all, it is
    equivalent to the two non-inductive definitions of evenness that
    we had already seen, and does not seem to offer any concrete
    benefit over them.  To give a better sense of the power of
    inductive definitions, we now show how to use them to model a
    classic concept in computer science: _regular expressions_. *)

(** Regular expressions are a simple language for describing strings,
    defined as follows: *)

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2], then [App re1
        re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s], then [Union re1
        re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation of
        a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i], then
        [Star re] matches [s].

        As a special case, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows: *)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

(** Again, for readability, we can also display this definition using
    inference-rule notation.  At the same time, let's introduce a more
    readable infix notation. *)

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

(** Notice that these rules are not _quite_ the same as the informal
    ones that we gave at the beginning of the section.  First, we
    don't need to include a rule explicitly stating that no string
    matches [EmptySet]; we just don't happen to include any rule that
    would have the effect of some string matching [EmptySet].  (Indeed,
    the syntax of inductive definitions doesn't even _allow_ us to
    give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

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

(** (Notice how the last example applies [MApp] to the strings [[1]]
    and [[2]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split the
    string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

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

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

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

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars (exp_match_ex1)  *)
(** The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* 请在此处解答 *) Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* 请在此处解答 *) Admitted.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (reg_exp_of_list_spec)  *)
(** Prove that [reg_exp_of_list] satisfies the following
    specification: *)


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)


(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

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

(** Something interesting happens in the [MStarApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re]), and a second one that applies when [x]
    occurs in [s2] (which matches [Star re]).  This is a good
    illustration of why we need induction on evidence for [exp_match],
    as opposed to [re]: The latter would only provide an induction
    hypothesis for strings that match [re], which would not allow us
    to reason about the case [In x s2]. *)

  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars (re_not_empty)  *)
(** Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it happily lets you try to set up an induction over a term
    that isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] can do), and leave you unable to
    complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt: *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct] than like [inversion].)

    We can solve this problem by generalizing over the problematic
    expressions with an explicit equality: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

Abort.

(** Invoking the tactic [remember e as x] causes Coq to (1) replace
    all occurrences of the expression [e] by the variable [x], and (2)
    add an equation [x = e] to the context.  Here's how we can use it
    to show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, which allows us to
    conclude immediately. *)

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re'], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.

  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced (pumping)  *)
(** One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

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

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

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

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

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
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [beq_nat_true_iff] lemma to the equation generated by
    destructing [beq_nat n m], to convert the assumption [beq_nat n m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [beq_nat n m].
    Instead of generating an equation such as [beq_nat n m = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence that
    [reflect P true] holds is by showing that [P] is true and using
    the [ReflectT] constructor.  If we invert this statement, this
    means that it should be possible to extract evidence for [P] from
    a proof of [reflect P true].  Conversely, the only way to show
    [reflect P false] is by combining evidence for [~ P] with the
    [ReflectF] constructor.

    It is easy to formalize this intuition and show that the two
    statements are indeed equivalent: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* 课上已完成 *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)


Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(** The new proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [apply] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, recommended (beq_natP_practice)  *)
(** Use [beq_natP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** In this small example, this technique gives us only a rather small
    gain in convenience for the proofs we've seen; however, using
    [reflect] consistently often leads to noticeably shorter and
    clearer scripts as proofs get larger.  We'll see many more
    examples in later chapters and in _Programming Language
    Foundations_.

    The use of the [reflect] property was popularized by _SSReflect_,
    a Coq library that has been used to formalize important results in
    mathematics, including as the 4-color theorem and the
    Feit-Thompson theorem.  The name SSReflect stands for _small-scale
    reflection_, i.e., the pervasive use of reflection to simplify
    small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, recommended (nostutter_defn)  *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from the [NoDup] property in 
    the exercise above: the sequence [1;4;1] repeats but does not
    stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* 请在此处解答 *)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* 请在此处解答 *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* 请在此处解答 *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* 请在此处解答 *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* 请在此处解答 *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 4 stars, optional (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)  *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* 请在此处解答 *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* 请在此处解答 *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* 请在此处解答 *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* 请在此处解答 *) Admitted.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* 请在此处解答 *)
.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* 请在此处解答 *) Admitted.
(** [] *)


(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represeneted
    as lists of ASCII characters: *)
Require Export Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)


(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. inversion H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros. 
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
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

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
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

(** **** Exercise: 3 stars, optional (app_ne)  *)
(** [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H2.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H. 
Qed.

(** **** Exercise: 3 stars, optional (star_ne)  *)
(** [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, optional (match_eps)  *)
(** Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (match_eps_refl)  *)
(** Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)


(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, optional (derive)  *)
(** Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
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

(** **** Exercise: 4 stars, optional (derive_corr)  *)
(** Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)


(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, optional (regex_match)  *)
(** Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (regex_refl)  *)
(** Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)


