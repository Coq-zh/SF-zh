(** * IndPrinciples: 归纳原理 *)

(** 理解了柯里-霍华德同构及其 Coq 实现之后，我们可以深入学习归纳原理。 *)

Set Warnings "-notation-overridden,-parsing".
Require Export ProofObjects.

(* ################################################################# *)
(** * 基础 *)

(** 每次我们使用 [Inductive] 来声明数据类型时，Coq 会自动为这个类型生成
    _'归纳原理'_。这个归纳原理也是定理：如果归纳地定义了 [t]，那么对应的
    归纳原理是 [t_ind]。这个自然数的归纳原理： *)

Check nat_ind.
(*  ===> nat_ind :
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

(** [induction] 策略是对归纳原理的直接包装，其内核，仅仅是执行 [apply t_ind]。
    为了清楚地理解这一点，让我们直接使用 [apply nat_ind] 而非 [induction]
    策略来做一些证明。比如说，这是我们在章节 [Basics]
    中见过的一个定理的另一种证明。 *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.

(** 这个证明基本上等同于之前的，但有几点区别值得注意。

    首先，在证明的归纳步骤（["S"] 情形）中，我们不得不手动管理变量名（即 [intros]），
    而 [induction] 会自动完成这些。

    其次，在应用 [nat_ind] 之前我们没有在上下文中引入 [n] —— [nat_ind] 的结论
    是一个量化的公式，[apply] 需要这个结论精确地匹配目标状态的形状，包括量词。
    相反，[induction] 策略对于上下文中的变量或目标中量化的变量都适用。

    相比于直接使用 [nat_ind] 这样的归纳原理，在实践中使用 [induction] 更加方便。
    但重要的是认识到除了这一点变量名的管理工作，我们在做的其实就是应用 [nat_ind]。 *)

(** **** 练习：2 星, optional (plus_one_r')  *)
(** 请不使用 [induction] 策略来完成这个证明。 *)

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** Coq 为每一个 [Inductive] 定义的数据类型生成了归纳原理，包括那些非递归的。
    尽管我们不需要使用归纳来证明非递归数据类型的性质，但归纳原理的概念仍然适用于它们：
    它提供了一种方法来证明对于这个类型所有值都成立的性质。

    这些生成的原则都具有类似的模式。如果我们定义了类型 [t] 及其构造子 [c1] ... [cn]，
    Coq 生成以下形状的定理：

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    每个情形具体的形状取决于对应构造子的参数。在写下一般的规则之前，
    让我们看看更多的例子。首先是一个无参数构造子的例子： *)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(** **** 练习：1 星, optional (rgb)  *)
(** 请写出对这个数据类型 Coq 将会生成的归纳原理。在纸上或注释中写下你的答案，
    然后同 Coq 打印的结果比较。 *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(** [] *)

(** 这是另一个例子，这一次其中一个构造子含有多个参数。*)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> (除了一些变量被重命名了)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist),
            P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(** **** 练习：1 星, optional (natlist1)  *)
(** 假设我们写下的定义和上面的有一些区别： *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** 现在归纳原理会是什么呢？ *)
(** [] *)

(** 对于这些例子，我们可以总结出一般的规则：

    - 类型定义给定了若干构造子；每个对应于归纳原理中的一个语句。
    - 每个构造子 [c] 有参数类型 [a1] ... [an]。
    - 每个 [ai] 要么是 [t]（我们定义的数据类型），要么是其他的类型 [s]。
    - 对应的归纳原理情形则是：

        - “对于所有的类型为 [a1]...[an] 的值 [x1]...[xn]，如果 [P] 对每个
          归纳的参数（每个具有类型 [t] 的 [xi]）都成立，那么 [P] 对于 [c x1 ... xn]
          成立”。
*)

(** **** 练习：1 星, optional (byntree_ind)  *)
(** 请写出对这个数据类型 Coq 将会生成的归纳原理。（与之前一样，在纸上或注释中写下你的答案，
    然后同 Coq 打印的结果比较。） *)

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf  : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.
(** [] *)

(** **** 练习：1 星, optional (ex_set)  *)
(** 这是对一个归纳定义的集合的归纳原理。

      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e

    请写出使用 [Inductive] 来定义的 [ExSet]： *)

Inductive ExSet : Type :=
  (* 请在此处解答 *)
.
(** [] *)

(* ################################################################# *)
(** * 多态 *)

(** 接下来，多态数据结构会是怎样呢？

    归纳定义的多态列表

      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.

    同 [natlist] 是十分相似的。主要的区别是，这里，全部的定义是由集合 [X] _'参数化'_的：
    也即，对于每个 [X] 我们定义了_'一族'_归纳类型 [list X]。
    （请注意，当 [list] 出现在声明体中时，它总是被应用参数 [x]。）
    归纳原理同样被 [X] 所参数化：

      list_ind :
        forall (X : Type) (P : list X -> Prop),
           P [] ->
           (forall (x : X) (l : list X), P l -> P (x :: l)) ->
           forall l : list X, P l

    请注意_'全部的'_归纳原理都被 [X] 所参数化。也即，[list_ind] 可认为是一个
    多态函数，当被应用类型 [X] 时，返回特化在类型 [list X] 上的归纳原理。 *)

(** **** 练习：1 星, optional (tree)  *)
(** 请写出对这个数据类型 Coq 将会生成的归纳原理。同 Coq 打印的结果比较你的答案。*)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.
(** [] *)

(** **** 练习：1 星, optional (mytype)  *)
(** 请找到对应于以下归纳原理的归纳定义：

      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m
*) 
(** [] *)

(** **** 练习：1 星, optional (foo)  *)
(** 请找到对应于以下归纳原理的归纳定义：

      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2
*) 
(** [] *)

(** **** 练习：1 星, optional (foo')  *)
(** 请考虑以下归纳定义： *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(** Coq 会为 [foo'] 生成什么归纳原理？请填写下面的空白，并使用 Coq 检查你的答案。

     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ ->
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
*)

(** [] *)

(* ################################################################# *)
(** * 归纳假设 *)

(** “归纳假设”是在什么语境下出现的呢？

    对于数的归纳原理：

       forall P : nat -> Prop,
            P 0  ->
            (forall n : nat, P n -> P (S n))  ->
            forall n : nat, P n

  是一个对于所有命题 [P] （或者，严格来说，对于被数字 [n] 索引的全部命题 [P]）
  成立的泛化陈述。每次我们使用这个原理，我们选择一个类型为 [nat->Prop]
  的表达式为 [P]。

  通过命名这个表达式，我们可以让归纳证明更加明确。比如，除了陈述定理
  [mult_0_r] 为 “[forall n, n * 0 = 0]”，我们还可以写成
  “[forall n, P_m0r n]”，其中 [O_m0r] 定义为…… *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

(** …… 或等价地： *)

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

(** 现在看看 [P_m0r] 在证明中的哪里出现。 *)

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* 请注意目前的证明状态！ *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(** 这一步额外的命名步骤并不是我们在证明中通常会做的，但对一两个例子显式地
    做这件事是由好处的，帮助我们清晰地看到哪个是归纳假设。
    如果对 [n] 归纳来证明 [forall n, P_m0r n]（使用 [induction]
    或 [apply nat_ind]），可以看到第一个子目标要求我们证明 [P_m0r 0]
    （“[P] 对零成立”），而第二个子目标要求我们证明 [forall n', P_m0r n' -> P_m0r (S n')]
    （也即，“[P] 对 [S n'] 成立如果其对 [n'] 成立”，或者说，“[P] 被 [S] 保持”）。
    _'归纳假设'_是后一个蕴含式中的前提——假设 [P] 对 [n'] 成立，这是我们在证明 [P]
    对 [S n'] 的过程中允许使用的。 *)

(* ################################################################# *)
(** * 深入 [induction] 策略 *)

(** [induction] 策略事实上为我们做了更多低层次的工作。

    请回忆一下自然数归纳原理的非形式化陈述：
      - 如果 [P n] 是某个涉及到数字 n 的命题，我们想要证明 [P] 对于_'所有'_数字 n
        都成立，我们以如下方式推理：
          - 证明 [P 0] 成立
          - 证明如果 [P n'] 成立，那么 [P (S n')] 成立
          - 得出结论 [P n] 对所有 n 成立。
    因此，当我们以 [intros n] 和 [induction n] 开始一个证明，我们首先在告诉 Coq
    考虑一个_'特殊的'_ [n]（通过引入到上下文中），然后告诉它证明一些关于
    _'全体'_数字的性质（通过使用归纳）。

    在这种情况下，Coq 事实上在内部“二次一般化（re-generalize）”了我们归纳的变量。
    比如说，在原始的 [plus] 结合性的证明中……  *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ……我们首先引入全部3个变量到上下文中，或者说是
     “考虑任意的 [n]，[m] 和 [p]……” *)
  intros n m p.
  (* …… 我们现在使用 [induction] 策略来证明 [P n]
     （也即，[n + (m + p) = (n + m) + p]）对全体的 [n] 成立，
     也因此对于当前上下文中特殊的 [n] 也成立。 *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* 在 [induction] 生成的第二个子目标——“归纳步骤”——我们必须证明
       对全体 [n']，[P n'] 蕴含了 [P (S n')]。[induction]
       策略自动为我们引入了 [n'] 和 [P n'] 到上下文中，并保持 [P (S n')]
       为目标。 *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** 对目标中量化的变量应用 [induction] 同样可以工作。*)

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** 请注意 [induction] 留下 [m] 仍然绑定在目标中——也即，我们在归纳证明的陈述
    仍然是以 [forall m] 开始的。

    如果我们对目标中其他量词_'后'_的量化变量使用 [induction]，那么它会自动
    引入全部被量词绑定的变量到上下文中。 *)

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  (* 这次让我们对 [m] 而非 [n] 进行归纳…… *)
  induction m as [| m'].
  - (* m = O *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** 练习：1 星, optional (plus_explicit_prop)  *)
(** 以上面 [mult_0_r''] 的方式来重写 [plus_assoc']，[plus_comm'] 和它们的证明——
    也即，对于每个定理，给出一个明确的命题的 [Definition]，陈述定理并用归纳法证明这个
    定义的命题。 *)

(* 请在此处解答 *)
(** [] *)

(* ################################################################# *)
(** * [Prop] 中的归纳原理 *)

(** 之前，我们仔细学习了 Coq 为归纳定义的_'集合'_生成的归纳原理。 像 [ev]
    这样的归纳定义_'命题'_的归纳原理会复杂一点点。就全部归纳原理来说，我们想要
    通过使用 [ev] 的归纳原理并归纳地考虑 [ev] 中所有可能的形式来证明一些东西。
    然而，直观地讲，我们想要证明的东西并不是关于_'证据'_的陈述，而是关于
    _'数字'_的陈述：因此，我们想要让归纳原理允许通过对证据进行归纳来
    证明关于数字的性质。

    比如，根据我们前面所讲，你可能会期待这样归纳定义的 [ev]……

      Inductive ev : nat -> Prop :=
      | ev_0 : ev 0
      | ev_SS : forall n : nat, ev n -> ev (S (S n)).

    ……并给我们下面这样的归纳原理……

    ev_ind_max : forall P : (forall n : nat, ev n -> Prop),
         P O ev_0 ->
         (forall (m : nat) (E : ev m),
            P m E ->
            P (S (S m)) (ev_SS m E)) ->
         forall (n : nat) (E : ev n),
         P n E

     ……因为：

     - 因为 [ev] 被数字 [n] 所索引（任何 [ev] 的对象 [E] 都是某个数字 [n]
       是偶数的证据），命题 [P] 同时被 [n] 和 [E] 所参数化——也即，被用于证明断言的
       归纳原理涉同时及到数字和这个数字是偶数的证据。

     - 由于有两种方法来给出偶数性质的证据（因为 [ev] 有两个构造子），应用归纳原理生成
       了两个子目标：

         - 我们必须证明 [P] 对 [0] 和 [ev_0] 成立。

         - 我们必须证明，当 [n] 是一个数字且 [E] 是其偶数性质的证据，如果 [P]
           对 [n] 和 [E] 成立，那么它也对 [S (S n)] 和 [ev_SS n E] 成立。

     - 如果这些子目标可以被证明，那么归纳原理告诉我们 [P] 对所有的偶数 [n]
       和它们的偶数性质 [E] 成立。

    这比我们通常需要或想要的更灵活一点：它为我们提供了一种方式证明逻辑断言，
    其断言涉及到一些关于偶数的证据的性质，然而我们真正想要的是证明_'数字'_
    是偶数这样的性质——我们感兴趣的是关于数字的断言，而非关于证据。如果对于命题 [P]
    的归纳原理仅仅被 [n] 所参数化，且其结论是 [P] 对所有偶数 [n] 成立，那会方便许多：

       forall P : nat -> Prop,
       ... ->
       forall n : nat,
       even n -> P n

    出于这样的原因，Coq 实际上为 [ev] 生成了简化过的归纳原理： *)

Check ev_ind.
(* ===> ev_ind
        : forall P : nat -> Prop,
          P 0 ->
          (forall n : nat, ev n -> P n -> P (S (S n))) ->
          forall n : nat,
          ev n -> P n *)

(** 请特别注意，Coq 丢弃了命题 [P] 参数中的证据项 [E]。 *)

(** 用中文表达 [ev_ind] 是说：

    - 假设，[P] 是关于自然数的一个性质（也即，[P n] 是一个在全体 [n] 上的 [Prop]）。
      为了证明当 [n] 是偶数时 [P n] 成立，需要展示：

      - [P] 对 [0] 成立，

      - 对任意 [n]，如果 [n] 是偶数且 [P] 对 [n] 成立，那么 [P] 对 [S (S n)] 成立。 *)

(** 正如期待的那样，我们可以不使用 [induction] 而直接应用 [ev_ind]。
    比如，我们可以使用它来证明 [ev']（那个在 [IndProp] 一章的练习中有点笨拙的偶数性质的定义）
    等价于更简洁的归纳定义 [ev]： *)
Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

(** [Inductive] 定义的具体形式会影响到 Coq 生成的归纳原理。

    比如在 [IndProp] 一章中，我们这样定义 [<=]： *)

(* Inductive le : nat -> nat -> Prop :=
     | le_n : forall n, le n n
     | le_S : forall n m, (le n m) -> (le n (S m)). *)

(** 这个定义其实可以被稍微简化一点，通过观察到左侧的参数 [n]
    在定义中始终是相同的，我们可把它变成整体定义中的一个“一般参数”，而非每个构造子的参数。*)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** 尽管第二个看起来不那么对称了，但它却更好一点。为什么呢？因为它会生成更简单的归纳原理。 *)

Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)

(* ################################################################# *)
(** * 形式化 vs. 非形式化的归纳证明 *)

(** 问：命题 [P] 的形式化证明和同一个命题 [P] 的非形式化证明之间是什么关系？

    答：后者应当_'教给'_读者如何产生前者。

    问：需要多少的细节？

    不幸的是，并没有一个正确的答案；当然了，其实有一系列的选择。

    一种选择是，我们可以为读者给出全部的形式化证明（也即，“非形式化的”证明只是把
    形式化的证明用文字表述出来）。这可能让读者有能力自己完成形式化的证明，但也许
    并没有_'教给'_读者什么东西。

  而另一种选择则是，我们可以说“某个定理为真，如果你觉得它有些困难那么可以自己尝试把它搞明白。”
  这也不是一种很好的教学策略，因为书写证明常常需要一两个对于要证明的东西的重要洞察，
  而多数读者往往在自己发现这些这些洞察前已经放弃了。

  一种中庸之道是——我们提供含有重要洞察的证明（免去读者像我们一开始一样辛苦地寻找证明），
  加上模式化部分的高层次建议（比如，归纳假设是什么，以及归纳证明中每个情形的证明责任），
  这样帮助读者节省自己重新构造这些东西的时间，但不会有过多的细节以至于主要的概念和想法受到干扰。

  我们在本章中已经仔细查看了形式化的归纳证明的“底层原理”，现在是时候来看看非形式化的归纳证明了。

  在现实世界的数学交流中，证明的书写既有冗长的，也有非常简洁的。
  尽管理想状态是二者中间的某种形式，但从有一点冗长的证明开始学习是有好处的。
  同时，在学习的过程中，有一个明确的标准来进行比较也是有益的。为此，
  我们提供了两份模板——一份用于归纳证明_'数据'_（也即，[Type] 中我们进行归纳的东西），
  另一份用于归纳证明_'证据'_（也即，[Prop] 中归纳定义的东西）。*)

(* ================================================================= *)
(** ** 对归纳定义的集合进行归纳 *)

(** _'模板'_：

       - _'定理'_： <有形如“For all [n:S], [P(n)]”的全称量化命题，其中 [S]
          是某个归纳定义的集合。>

         _'证明'_： 对 [n] 进行归纳。

           <[S] 中的每个构造子 [c] 的情形……>

           - 假设 [n = c a1 ... ak]，其中 <…… 这里我们为每个具有类型 [S] 的 [a] 陈述其归纳假设（IH）> 。
             我们需要证明 <…… 我们在这里重新陈述 [P(c a1 ... ak)]>。

             <继续并证明 [P(n)] 来完成这个情形……>

           - <其他情形以此类推……>                        []

    _'举例'_:

      - _'定理'_: 对所有集合 [X]， 列表 [l : list X]，以及数字 [n]，如果
          [length l = n] 那么 [index (S n) l = None]。

        _'证明'_: 对 [l] 进行归纳。

        - 假设 [l = []]。我们需要证明，对于任意数字 [n]，如果 [length [] = n]，那么
         [index (S n) [] = None]。

          可从 [index] 的定义中直接得出。

        - 假设 [l = x :: l'] 对某个 [x] 和 [l']，其中 [length l' = n'] 对任意数字 [n']
          蕴含了 [index (S n') l' = None]。我们需要证明，对任意数字 [n]，如果
          [length (x::l') = n] 那么 [index (S n) (x::l') = None]。

          设 [n] 为数字且 [length l = n]。因为

            length l = length (x::l') = S (length l'),

          需要证明

            index (S (length l')) l' = None.

          若选取 [n'] 为 [length l'] 这可从归纳假设中直接得出。  [] *)

(* ================================================================= *)
(** ** 对归纳定义的命题进行归纳 *)

(** 由于归纳定义的证明对象经常被称作“导出树（derivation trees）”，这种形式的
    证明也被叫做_'在导出式上归纳'_。
    _'模板'_：

       - _'定理'_: <有形如“[Q -> P]”的命题，其中 [Q] 是某个归纳定义的命题
        （更一般地，“对任意 [x] [y] [z]，[Q x y z -> P x y z]”）>

         _'证明'_: 对 [Q] 的导出式进行归纳。<或者，更一般地，“假设给定 [x]，[y] 和
         [z]。通过对 [Q x y z] 的导出式进行归纳，我们证明 [Q x y z] 蕴含 [P x y z]”……>

           <[Q] 中的每个构造子 [c] 的情形……>

           - 假设被用于证明 [Q] 的最终规则是 [c]。那么<……我们在这里陈述所有 [a] 的类型，
            从构造子的定义中得到的任何等式，以及每个具有类型 [Q] 的 [a] 的归纳假设>。
            我们需要证明<……我们在这里重新陈述 [P]>。

             <继续并证明 [P] 来完成这个情形……>

           - <其他情形以此类推……>                        []

    _'举例'_

       - _'定理'_: [<=] 关系是传递的——也即，对任意数字 [n]，[m] 和 [o]，如果
         [n <= m] 且 [m <= o] 那么 [n <= o]。

         _'证明'_: 对 [m <= o] 的导出式进行归纳。

           - 假设被用于证明 [m <= o] 的最终规则是 [le_n]。
             那么 [m = o] 且我们需要证明 [n <= m]，其可从假设中直接得出。

           - 假设被用于证明 [m <= o] 的最终规则是 [le_S]。
             那么 [o = S o'] 对某个 [o'] 且 [m <= o']。我们需要证明 [n <= S o']。
             由归纳假设得出，[n <= o']。

            因此，根据 [le_S]，[n <= S o']。  [] *)

