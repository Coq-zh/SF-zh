(** * Tactics: 更多基本策略 *)

(** 本章额外介绍了一些证明策略和手段，
    它们能用来证明更多关于函数式程序的有趣性质。我们会看到：

    - 如何在“向前证明”和“向后证明”两种风格中使用辅助引理；
    - 如何对数据构造子进行论证（特别是，如何利用它们单射且不交的事实）；
    - 如何增强归纳假设（以及何时需要增强）；
    - 还有通过分类讨论进行论证的更多细节。 *)

Set Warnings "-notation-overridden,-parsing".
Require Export Poly.

(* ################################################################# *)
(** * [apply] 策略 *)

(** 我们经常会遇到待证目标与上下文中的前提或已证引理_'刚好相同'_的情况。 *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(** 我们可以像之前那样用“[rewrite -> eq2.  reflexivity.]”来完成。
    不过如果我们使用 [apply] 策略，只需一步就能达到同样的效果： *)

  apply eq2.  Qed.

(** [apply] 策略也可以配合_'条件（Conditional）'_假设和引理来使用：
    如果被应用的语句是一个蕴含式，那么该蕴含式的前提就会被添加到待证子目标列表中。 *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** 通常，当我们使用 [apply H] 时，语句 [H] 会以一个绑定了某些
    _'通用变量（Universal Variables）'_ 的 [forall] 开始。在 Coq 针对 [H]
    的结论匹配当前目标时，它会尝试为这些变量查找适当的值。例如，
    当我们在以下证明中执行 [apply eq2] 时，[eq2] 中的通用变量 [q]
    会以 [n] 实例化，而 [r] 会以 [m] 实例化。 *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** 练习：2 星, optional (silly_ex)  *)
(** 请完成以下证明，不要使用 [simpl]。 *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 要使用 [apply] 策略，被应用的事实（的结论）必须精确地匹配证明目标：
    例如, 当等式的左右两边互换后，[apply] 就无法起效了。 *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.

(** 在这里，我们无法直接使用 [apply]，不过我们可以用 [symmetry] 策略
    它会交换证明目标中等式的左右两边。 *)

  symmetry.
  simpl. (* （此处的 [simpl] 是可选的，因为 [apply] 会在需要时先进行化简。） *)
  apply H.  Qed.

(** **** 练习：3 星 (apply_exercise1)  *)
(** （_'提示'_：你可以配合之前定义的引理来使用 [apply]，不仅限于当前上下文中的前提。
    记住 [Search] 是你的朋友。） *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, optional (apply_rewrite)  *)
(** 简述 [apply] 与 [rewrite] 策略之区别。哪些情况下二者均可有效利用？ *)

(* 请在此处解答 *)
(** [] *)

(* ################################################################# *)
(** * [apply ... with ...] 策略 *)

(** 以下愚蠢的例子在一行中使用了两次改写来将 [[a,b]] 变成 [[e,f]]。 *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** 由于这种模式十分常见，因此我们希望一劳永逸地把它作为一条引理记录下来，
    即等式具有传递性。 *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** 现在，按理说我们应该可以用 [trans_eq] 来证明前面的例子了。
    然而，为此我们还需要稍微改进一下 [apply] 策略。 *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

(** 如果此时我们只是告诉 Coq [apply trans_eq]，那么它会
    （根据该引理的结论对证明目标的匹配）说 [X] 应当实例化为 [[nat]]、[n]
    实例化为 [[a,b]]、以及 [o] 实例化为 [[e,f]]。然而，匹配过程并没有为
    [m] 确定实例：我们必须在 [apply] 的调用后面加上 [with (m:=[c,d])]
    来显式地提供一个实例。 *)

  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

(** 实际上，我们通常不必在 [with] 从句中包含名字 [m]，Coq
    一般足够聪明来确定我们给出的实例。我们也可以写成：
    [apply trans_eq with [c;d]]。 *)

(** **** 练习：3 星, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * [inversion] 策略 *)

(** 回想自然数的定义：

     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

    我们可从该定义中观察到，所有的数都是两种形式之一：要么是构造子 [O]，
    要么就是将构造子 [S] 应用到另一个数上。不过这里还有无法直接看到的：
    自然数的定义（以及我们对其它编程语言中数据类型声明的工作方式的非形式化理解）
    中还蕴含了两个事实：

    - 构造子 [S] 是_'单射（Injective）'_的。
      即，如果 [S n = S m]，那么 [n = m] 必定成立。

    - 构造子 [O] 和 [S] 是_'不相交（Disjoint）'_的。
      即，对于任何 [n]，[O] 都不等于 [S n]。

    类似的原理同样适用于所有归纳定义的类型：所有构造子都是单射的，
    而不同构造子构造出的值绝不可能相等。对于列表来说，[cons] 构造子是单射的，
    而 [nil] 不同于任何非空列表。对于布尔值来说，[true] 和 [false] 是不同的。
    因为 [true] 和 [false] 二者都不接受任何参数，它们的单射性并不有趣。
    其它归纳类型亦是如此。 *)

(** Coq 提供了名为 [inversion]（反演）的策略，它允许我们在证明中利用这些原理。
    要了解如何使用它，我们来明确地展示 [S] 构造子是单射的： *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** 我们在此处写下 [inversion H] 来要求 Coq 生成所有可以从 [H]
    推断出来的等式作为附加前提，并以此来替换证明目标中的变量。在本例中，
    这相当于添加了一个新的前提 [H1 : n = m] 并将证明目标中的 [n] 替换成了 [m]。 *)

  inversion H.
  reflexivity.
Qed.

(** 下面是个更有趣的例子，它展示了如何一次推导出多个等式。 *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

(** 我们可以用 [as ...] 从句为 [inversion] 生成的等式命名： *)

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity.  Qed.

(** **** 练习：1 星 (inversion_ex3)  *)
Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 当在涉及到_'不同'_构造子相等性的前提上使用 [inversion] 时（如 [S n = O]），
    它会立即解决证明目标。考虑以下证明： *)

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n.

(** 我们可以通过对 [n] 进行分类讨论来继续。第一种分类是平凡的。 *)

  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.

(** 然而，第二种情况看起来并没有那么简单：假设 [beq_nat 0 (S n') = true]
    我们必须证明 [S n' = 0], 但后者显然矛盾！继续证明的思路依赖于该假设。
    在简化待证目标的陈述后，我们就会看到 [beq_nat 0 (S n') = true] 会变成
    [false = true]： *)

  - (* n = S n' *)
    simpl.

(** 如果我们对此前提使用 [inversion] ，Coq 就会注意到我们试图证明的子目标是不可能的，
    然后把它从进一步的考虑中移除。 *)

    intros H. inversion H. Qed.

(** 本例是逻辑学原理_'爆炸原理'_的一个实例，它断言矛盾的前提会推出任何东西，
    甚至是假命题！ *)

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

(** 如果你对爆炸原理感到困惑，请记住这些证明并不会真的展示出该语句的结论成立。
    相反，它认为，如果前提所描述的无意义的情况确实出现了，那么无意义的结论就会随之而来。
    我们会在下一章中探讨更多爆炸原理的详情。 *)

(** **** 练习：1 星 (inversion_ex6)  *)
Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 要总结这一讨论，假设 [H] 是上下文中的前提，或者是之前已经证明的，
    关于构造子 [c] 和 [d] 以及参数 [a1 ... an] 和 [b1 ... bm] 的，形如

        c a1 a2 ... an = d b1 b2 ... bm

    的引理。那么 [inversion H] 会产生以下效果：

    - 若 [c] 和 [d] 为相同的构造子，那么根据该构造子的单射性，我们知道
      [a1 = b1]、[a2 = b2] 等等。[inversion H] 会将这些事实添加到上下文中，
      并尝试用它们来改写证明目标。

    - 若 [c] 和 [d] 为不同的构造子，那么前提 [H] 是矛盾的，
      当前证明目标完全不用考虑。此时，[inversion H] 会将当前证明目标标记为已完成，
      并将它从证明目标栈中弹出。 *)

(** 构造子的单射性允许我们论证 [forall (n m : nat), S n = S m -> n = m]。
    此蕴含式的交流（converse）是一个更加一般的关于构造子和函数的事实的实例，
    在后面的几个地方我们会发现它很方便： *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(** * 对前提使用策略 *)

(** 默认情况下，大部分策略会作用于目标公式并保持上下文不变。然而，
    大部分策略还有对应的变体来对上下文中的语句执行类似的操作。

    例如，策略 [simpl in H] 会对上下文中名为 [H] 的前提执行化简。 *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** 类似地，[apply L in H] 会针对上下文中的前提 [H] 匹配某些
    （形如 [L1 -> L2] 中的）条件语句 [L]。然而，与一般的 [apply] 不同
    （它将匹配 [L2] 的目标改写为子目标 [L1]），[apply L in H] 会针对
    [L1] 匹配 [H]，如果成功，就将其替换为 [L2]。

    换言之，[apply L in H] 给了我们一种“正向推理”的方式：根据 [L1 -> L2]
    和一个匹配 [L1] 的前提，它会产生一个匹配 [L2] 的前提。作为对比，[apply L]
    是一种“反向推理”：它表示如果我们知道 [L1 -> L2] 并且试图证明 [L2]，
    那么证明 [L1] 就足够了。

    下面是前面证明的一种变体，它始终使用正向推理而非反向推理。 *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5  ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** 正向推理从_'给定'_的东西开始（即前提、已证明的定理），
    根据它们迭代地刻画结论直到抵达目标。反向推理从_'目标'_开始，
    迭代地推理蕴含目标的东西，直到抵达前提或已证明的定理。
    如果你之前见过非形式化的证明（例如在数学或计算机科学课上），
    它们使用的应该是正向推理。通常，Coq 习惯上倾向于使用反向推理，
    但在某些情况下，正向推理更易于思考。 *)

(** **** 练习：3 星, recommended (plus_n_n_injective)  *)
(** 请在此证明中练习使用“in”形式的变体。（提示：使用 [plus_n_Sm]。） *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 变换归纳原理 *)

(** 在 Coq 中进行归纳证明时，有时控制归纳假设的确切形式是十分重要的。
    特别是，在调用 [induction] 策略前，我们用 [intros]
    将假设从目标移到上下文中时要十分小心。例如，假设我们要证明 [double]
    函数式单射的 -- 即，它将不同的参数映射到不同的结果：

    Theorem double_injective: forall n m,
      double n = double m -> n = m.

    其证明的_'开始方式'_有点微妙：如果我们以

      intros n. induction n.

    开始，那么一切都好。然而假如以

      intros n m. induction n.

    开始，就会卡在归纳情况中... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *) apply f_equal.

(** 此时，归纳假设 [IHn'] _'不会'_给出 [n' = m'] -- 会有个额外的 [S] 阻碍 --
    因此该目标无法证明。 *)

      Abort.

(** 哪里出了问题？ *)

(** 问题在于，我们在调用归纳假设的地方已经将 [m] 引入了上下文中 --
    直观上，我们已经告诉了 Coq“我们来考虑具体的 [n] 和 [m]...”，
    而现在必须为这些_'具体的'_ [n] 和 [m] 证明 [double n = double m]，
    然后才有 [n = m]。

    下一个策略 [induction n] 告诉 Coq：我们要对 [n] 归纳来证明该目标。
    也就是说，我们要证明对于_'所有的'_ [n]，命题

      - [P n] = "if [double n = double m], then [n = m]"

    成立，需通过证明

      - [P O]

        （即，若“[double O = double m] 则 [O = m]”）和

      - [P n -> P (S n)]

        （即，若“[double n = double m] 则 [n = m]”蕴含“若
        [double (S n) = double m] 则 [S n = m]”）来得出。

    如果我们仔细观察第二个语句，就会发现它说了奇怪的事情：即，对于一个_'具体的'_
    [m]，如果我们知道

      - “若 [double n = double m] 则 [n = m]”

    那么我们就能证明

       - “若 [double (S n) = double m] 则 [S n = m]”。

    要理解为什么它很奇怪，我们来考虑一个具体的 [m] --
    比如说，[5]。该语句就会这样说：如果我们知道

      - [Q] = “若 [double n = 10] 则 [n = 5]”

    那么我们就能证明

      - [R] = “若 [double (S n) = 10] 则 [S n = 5]”。

    但是知道 [Q] 对于证明 [R] 来说并没有任何帮助！（如果我们试着根据 [Q]
    证明 [R] from [Q]，就会以“假设 [double (S n) = 10]..”这样的句子开始，
    不过之后我们就会卡住：知道 [double (S n)] 为 [10] 并不能告诉我们
    [double n] 是否为 [10]，因此 [Q] 是没有用的。） *)

(** 当 [m] 已经在上下文中时，试图对 [n] 进行归纳来进行此证明是行不通的，
    因为我们之后要尝试证明涉及_'每一个'_ [n] 的关系，而不只是_'单个'_ [m]。 *)

(** 对 [double_injective] 的成功证明将 [m] 留在了目标语句中 [induction]
    作用于 [n] 的地方：*)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.

  - (* n = S n' *) simpl.

(** 注意，此时的证明目标和归纳假设是不同的：证明目标要求我们证明更一般的事情
    （即，为_'每一个'_ [m] 证明该语句），而归纳假设 [IH] 相应地更加灵活，
    允许我们在应用归纳假设时选择任何想要的 [m]。 *)

    intros m eq.

(** 现在我们选择了一个具体的 [m] 并引入了假设 [double n = double m]。
    由于我们对 [n] 做了情况分析，因此还要对 [m] 做情况分析来保持两边“同步”。 *)

    destruct m as [| m'].
    + (* m = O *) simpl.

(** 0 的情况很显然： *)

      inversion eq.

    + (* m = S m' *)
      apply f_equal.

(** 到这里，由于我们在 [destruct m] 的第二个分支中，因此上下文中涉及到的 [m']
    就是我们开始讨论的 [m] 的前趋。由于我们也在归纳的 [S] 分支中，这就很完美了：
    如果我们在归纳假设中用当前的 [m']（此实例由下一步的 [apply] 自动产生）
    实例化一般的 [m]，那么 [IHn'] 就刚好能给出我们需要的来结束此证明。 *)

      apply IHn'. inversion eq. reflexivity. Qed.

(** 我们需要小心使用归纳来试图证明某些过于具体的东西，而你应该从中解脱出来：
    要通过对 [n] 进行归纳来证明 [n] 和 [m] 的性质，有时保留 [m] 的一般性是很重要的。 *)

(** 以下练习需要同样的模式。 *)

(** **** 练习：2 星 (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, advanced (beq_nat_true_informal)  *)
(** 给出一个详细的 [beq_nat_true] 的非形式化证明，量词要尽可能明确。 *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_informal_proof : option (prod nat string) := None.

(* 请在此处解答 *)
(** [] *)

(** 在 [induction] 之前做一些 [intros] 来获得更一般归纳假设并不总是奏效。
    有时需要对量化的变量做一下_'重排'_。例如，假设我们想要通过对 [m]
    而非 [n] 进行归纳来证明 [double_injective]。 *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
        (* 和前面一样，又卡在这儿了。 *)
Abort.

(** 问题在于，要对 [m] 进行归纳，我们首先必须对 [n] 归纳。
    （如果我们不引入任何东西就执行 [induction m]，Coq 就会自动为我们引入 [n]！） *)

(** 我们可以对它做什么？一种可能就是改写该引理的陈述使得 [m] 在 [n] 之前量化。
    这样是可行的，不过它不够好：我们不想调整该引理的陈述来适应具体的证明策略！
    我们更想以最清晰自然的方式陈述它。 *)

(** 我们可以先引入所有量化的变量，然后_'重新一般化（re-generalize）'_
    其中的一个或几个，选择性地从上下文中挑出几个变量并将它们放回证明目标的开始处。
    用 [generalize dependent] 策略就能做到。*)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* 现在 [n] 回到了目标中，我们可以对 [m] 进行归纳并得到足够一般的归纳假设了。 *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(** 我们来看一下此定理的非形式化证明。注意我们保持 [n]
    的量化状态并通过归纳证明的命题，对应于我们形式化证明中依赖的一般化。

    _'定理'_：对于任何自然数 [n] 和 [m]，若 [double n = double m]，则 [n = m]。

    _'证明'_：令 [m] 为一个 [nat]。我们通过对 [m] 进行归纳来证明，对于任何 [n]，
        若 [double n = double m]，则 [n = m]。

      - 首先，设 [m = 0]，而 [n] 是一个数使得 [double n = double m]。
        我们必须证明 [n = 0]。

        由于 [m = 0]，根据 [double] 的定义，我们有 [double n = 0]。此时对于 [n]
        需要考虑两种情况。若 [n = 0]，则得证，因为 [m = 0 = n]，正如所需。
        否则，若对于某个 [n'] 有 [n = S n']，我们就会导出矛盾：根据 [double]
        的定义，我们可得出 [double n = S (S (double n'))]，但它与 [double n = 0]
        相矛盾。

      - 其次，设 [m = S m']，而 [n] 同样是一个数使得 [double n = double m]。
        我们必须证明 [n = S m']，根据归纳假设，对于任何数 [s]，若
        [double s = double m']，则 [s = m']。

        根据 [m = S m'] 的事实以及 [double] 的定义我们有 [double n = S (S (double m'))]。
        此时对于 [n] 需要考虑两种情况。

        若 [n = 0]，则根据 [double n = 0] 的定义会得出矛盾。

        因此，我们假设对于某个 [n']，有 [n = S n']，同样根据 [double]
        的定义，我们有 [S (S (double n')) = S (S (double m'))]，它可通过反演
        [double n' = double m'] 得出。以 [n'] 实例化归纳假设允许我们得出
        [n' = m'] 的结论，显然 [S n' = S m']。因此 [S n' = n] 且 [S m' = m]，
        此即我们所欲证。 [] *)

(** 在结束本节去做习题之前，我们先稍微跑个题，使用 [beq_nat_true]
    来证明一个标识符的类似性质以备后用： *)

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(** **** 练习：3 星, recommended (gen_dep_practice)  *)
(** 通过对 [l] 进行归纳来证明它。 *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 展开定义 *)

(** 有时我们需要手动展开（unfold）定义一边处理右式。例如，如果我们定义了... *)

Definition square n := n * n.

(** ...并试图证明一个关于 [square] 的简单事实... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ...那么就会卡住：此时 [simpl] 无法化简任何东西，而由于我们尚未证明任何关于
    [square] 的事实，也就没有任何可以用来 [apply] 或 [rewrite] 的东西。

    为此，我们可以手动用 [unfold] 展开 [square] 的定义： *)

  unfold square.

(** 现在我们有很多工作要做：等式两边都是涉及乘法的表达式，
    而我们有很多可用的关于乘法的事实。特别是，我们知道它满足交换性和结合性，
    根据这些事实，此引理不难证明。 *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** 在这一点上，展开和简化的深入讨论一切顺利。

    你可能已经观察到了像 [simpl]、[reflexivity] 和 [apply] 这样的策略，
    通常总会在需要时自动展开函数的定义。例如，若我们将 [foo m] 定义为常量 [5]... *)

Definition foo (x: nat) := 5.

(** 那么在以下证明中 [simpl]（或 [reflexivity]，如果我们忽略 [simpl]）
    就会将 [foo m] 展开为 [(fun x => 5) m] 并进一步将其化简为 [5]。 *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** 然而，这种自动展开较为保守。例如，若我们用模式匹配定义稍微复杂点的函数... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...那么类似的证明就会被卡住： *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* 啥也没做！ *)
Abort.

(** [simpl] 没有进展的原因在于，它注意到在试着展开 [bar m] 之后会留下被匹配的
    [m]，它是一个变量，因此 [match] 无法被进一步化简。（它还没有聪明到发现
    [match] 的两个分支是完全相同的。）因此它会放弃展开 [bar m] 并留在那。
    类似地，在试着展开 [bar (m+1)] 时会留下一个 [match]，被匹配者是一个函数应用
    （即它本身，即便在展开 [+] 的定义后也无法被化简），因此 [simpl] 会留下它。 *)

(** 此时有两种方法可以继续。一种是用 [destruct m] 将证明分为两种情况，
    每一种都关注于更具体的 [m]（[O] vs [S _]）。在这两种情况下，
    [bar] 中的 [match] 可以继续了，证明则很容易完成。 *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** 这种方法是可行的，不过它依赖于我们能发现隐藏在 [bar] 中的 [match]
    阻碍了证明的进展。 *)

(** 一种更直白的方式就是明确地告诉 Coq 去展开 [bar]。 *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** 现在很明显，我们在 [=] 两边的 [match] 上都卡住了，不用多想就能用
    [destruct] 来结束证明。 *)

  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * 对复合表达式使用 [destruct] *)

(** 我们已经见过许多通过 [destruct] 进行情况分析来处理一些变量的值了。
    不过有时我们需要根据某些_'表达式'_的结果的情况来进行推理。我们也可以用
    [destruct] 来做这件事。

    下面是一些例子：*)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity.  Qed.

(** 在前面的证明中展开 [sillyfun] 后，我们发现卡在
    [if (beq_nat n 3) then ... else ...] 上了。但由于 [n] 要么等于 [3]
    要么不等于，因此我们可以用 [destruct (beq_nat n 3)] 来对这两种情况进行推理。

    通常，[destruct] 策略可用于对任何计算结果进行情况分析。如果 [e]
    是某个表达式，其类型为归纳定义的类型 [T]，那么对于 [T] 的每个构造子
    [c]，[destruct e] 都会生成一个子目标，其中（即目标和上下文中）所有的
    [e] 都会被替换成 [c]。*)

(** **** 练习：3 星, optional (combine_split)  *)
(** 以下是 [Poly] 一章中出现过的 [split] 函数的实现： *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(** 请证明 [split] 和 [combine] 在以下概念下互为反函数： *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 然而，用 [destruct] 解构复合表达式需要小心，因为有时 [destruct]
    会擦除我们需要用来完成证明的信息。 *)
(** 例如，假设函数 [sillyfun1] 定义如下： *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** 现在假设我们想要说服 Coq 接受一个（相当明显的）事实，
    即 [sillyfun1 n] 仅当 [n] 为奇数时才返回 [true]。仿照我们前面对
    [sillyfun] 的证明，自然要像下面这样开始： *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* 卡住了... *)
Abort.

(** 我们在这里卡住了，因为上下文中没有足够的信息来证明此目标！
    因为 [destruct] 进行的代换太粗暴了 -- 它丢弃了所有的 [beq_nat n 3]，
    然而我们需要保留一些对该表达式的记忆以及它被解构的方法，
    因为我们需要能够去推理它，由于情况分析中此分支的 [beq_nat n 3 = true]，
    那么一定有 [n = 3]，据此可得 [n] 为奇数。

    我们真正想要的是将所有存在的 [beq_nat n 3] 都代换掉，
    但同时还要在上下文中添加一个等式来记录我们在哪种情况中。[eqn:]
    限定符允许我们引入这样一个等式，并为它取一个名字。 *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* 现在我们的状态和前面卡住的地方一样了，除了上下文中包含了额外的相等性假设，
     它就是我们继续推进所需要的。 *)
    - (* e3 = true *) apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* 当我们到达正在推理的函数体中第二个相等性测试时，我们可以再次使用
        [eqn:]，以便结束此证明。 *)
      destruct (beq_nat n 5) eqn:Heqe5.
        + (* e5 = true *)
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq.  Qed.

(** **** 练习：2 星 (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 复习 *)

(** 现在我们已经见过 Coq 中最基础的策略了。未来的章节中我们还会介绍更多，
    之后我们会看到一些更加强大的_'自动化'_策略，它能让 Coq 帮我们处理底层的细节。
    不过基本上我们已经有了完成工作所需的东西。

    下面是我们已经见过的：

      - [intros]：将前提/变量从证明目标移到上下文中

      - [reflexivity]：（当目标形如 [e = e] 时）结束证明

      - [apply]：用前提、引理或构造子证明目标

      - [apply... in H]：将前提、引理或构造子应用到上下文中的假设上（正向推理）

      - [apply... with...]：为无法被模式匹配确定的变量显式指定值

      - [simpl]：化简目标中的计算

      - [simpl in H]：化简前提中的计算

      - [rewrite]：使用相等性假设（或引理）来改写目标

      - [rewrite ... in H]：使用相等性假设（或引理）来改写前提

      - [symmetry]：将形如 [t=u] 的目标改为 [u=t]

      - [symmetry in H]：将形如 [t=u] 的前提改为 [u=t]

      - [unfold]：用目标中的右式替换定义的常量

      - [unfold... in H]：用前提中的右式替换定义的常量

      - [destruct... as...]：对归纳定义类型的值进行情况分析

      - [destruct... eqn:...]：为添加到上下文中的等式指定名字，
        记录情况分析的结果

      - [induction... as...]: 对归纳定义类型的值进行归纳

      - [inversion]：根据构造子的单射性和不同性进行推理

      - [assert (H: e)]（或 [assert (e) as H]）：引入“局部引理”[e]
        并称之为 [H]

      - [generalize dependent x]：将变量 [x]（以及任何依赖它的东西）
        从上下文中移回目标公式内的前提中 *)

(* ################################################################# *)
(** * 附加练习 *)

(** **** 练习：3 星 (beq_nat_sym)  *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced, optional (beq_nat_sym_informal)  *)
(** 根据前面你对该引理的形式化证明，给出与它对应的非形式化证明：

   定理：对于任何自然数 [n] [m]，[beq_nat n m = beq_nat m n].

   证明： *)
   (* 请在此处解答 *)
(** [] *)

(** **** 练习：3 星, optional (beq_nat_trans)  *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (split_combine)  *)
(** 在前面的练习中，我们证明了对于所有序对的列表，[combine] 是 [split]
    的反函数。你如何形式化陈述 [split] 是 [combine] 的反函数？何时此性质成立？

    请完成下面 [split_combine_statement] 的定义，其性质指出 [split]
    是 [combine] 的反函数。之后，证明该性质成立。（除必要的 [intros]
    之外，不要进行更多的 [intros]，以此来保证你的归纳假设的一般性。
    提示：你需要 [l1] 和 [l2] 的什么性质来保证
    [split] [combine l1 l2 = (l1,l2)] 成立？） *)

Definition split_combine_statement : Prop
  (* （“[: Prop]” 表示我们在这里给出了一个逻辑命题。） *)
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem split_combine : split_combine_statement.
Proof.
(* 请在此处解答 *) Admitted.
(* 请勿修改下面这一行： *)
Definition manual_grade_for_split_combine : option (prod nat string) := None.

(** [] *)

(** **** 练习：3 星, advanced (filter_exercise)  *)
(** 本练习有点难度。为你的归纳假设的形式花点心思。 *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced, recommended (forall_exists_challenge)  *)
(** 定义两个递归的 [Fixpoints]，[forallb] 和 [existsb]。
    第一个检查列表中的每一个元素是否均满足给定的断言：

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true

    第二个检查列表中是否存在一个元素满足给定的断言：

      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    接着，用 [forallb] 和 [negb] 定义一个 [existsb] 的非递归版本，名为 [existsb']。

    最后，证明定理 [existsb_existsb'] 指出 [existsb'] 和 [existsb] 的行为相同。 *)

(* 请在此处解答 *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_forall_exists_challenge : option (prod nat string) := None.
(** [] *)



