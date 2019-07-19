(** * Rel: 关系的性质 *)

(** 本章为可选章节，主要讲述了在 Coq 定义二元关系的一些基本方法和相关定理的证明。
    关键定义会在实际用到的地方复述（_'编程语言基础'_中的[Smallstep]一章），
    因此熟悉这些概念的读者可以略读或跳过本章。不过，这些内容也是对 Coq
    的证明功能很好的练习，因此在读完 [IndProp] 一章后，
    阅读本章也许会对你有所帮助。 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

(* ################################################################# *)
(** * 关系 *)

(** 集合 [X] 上的二元_'关系（Relation）'_指所有由两个 [X] 中的元素参数化的命题，
    即，有关一对 [X] 中的元素的命题。 *)

Definition relation (X: Type) := X -> X -> Prop.

(** 令人困惑的是，“关系”原本是个更为通用的词语，然而 Coq 标准库中的“关系”
    却单指这一种“某个集合中的元素之间二元关系”。为了与标准库保持一致，
    我们将会沿用这一定义。然而“关系”一词除了指这一意义以外，
    也可以指代任何数量的，可能是不同集合之间的更一般的关系。
    在讨论中使用“关系”一词时，应该在上下文中解释具体所指的含义。*)

(** 一个关系的例子是 [nat] 上的 [le]，即“小于或等于”关系，我们通常写作
    [n1 <= n2]。 *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
(** （为什么我们不直接写成 [Inductive le : relation nat...] 呢？
    这是因为我们想要将第一个 [nat] 放在 [:] 的左侧，这能让 Coq 为 [<=]
    更为友好的的归纳法则。） *)

(* ################################################################# *)
(** * 基本性质 *)

(** 学过本科离散数学课的人都知道，与关系相关的东西有很多，
    包括对关系的性质（如自反性、传递性等），关于某类关系的一般定理，
    如何从一种关系构造出另一种关系等等。例如： *)

(* ----------------------------------------------------------------- *)
(** *** 偏函数 *)

(** 对于集合 [X] 上的关系 [R] ，如果对于任何 [x] 最多只有一个 [y]
    使得 [R x y] 成立 -- 即，[R x y1] 和 [R x y2] 同时成立蕴含 [y1 = y2]，
    则称 [R] 为_'偏函数'_。 *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** 例如，之前定义的 [next_nat] 关系就是个偏函数。 *)

Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.

(** 然而，数值上的 [<=] 关系并不是个偏函数。（利用反证法，假设 [<=]
    是一个偏函数。然而根据其定义我们有 [0 <= 0] 和 [0 <= 1]，这样会推出
    [0 = 1]。这是不可能的，所以原假设不成立。） *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.

(** **** 练习：2 星, standard, optional (total_relation_not_partial)  

    请证明 [IndProp] 一章练习题中定义的 [total_relation] 不是偏函数。 *)

(* 请在此处解答 

    [] *)

(** **** 练习：2 星, standard, optional (empty_relation_partial)  

    请证明 [IndProp] 一章练习题中定义的 [empty_relation] 是偏函数。 *)

(* 请在此处解答 

    [] *)

(* ----------------------------------------------------------------- *)
(** *** 自反关系 *)

(** 集合 [X] 上的_'自反关系'_是指 [X] 的每个元素都与其自身相关。 *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.

(* ----------------------------------------------------------------- *)
(** *** 传递关系 *)

(** 如果 [R a b] 和 [R b c] 成立时 [R a c] 也成立，则称 [R] 为_'传递关系'_。 *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** 练习：2 星, standard, optional (le_trans_hard_way)  

    我们也可以不用 [le_trans]，直接通过归纳法来证明 [lt_trans]，
    不过这会耗费更多精力。请完成以下定理的证明。 *)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* 根据 [m] 小于 [o] 的证据用归纳法证明它。 *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (lt_trans'')  

    再将此定理证明一遍，不过这次要对 [o] 使用归纳法。 *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* 请在此处解答 *) Admitted.
(** [] *)

(** [le] 的传递性反过来也能用于证明一些之后会用到的事实，
    例如后面对反对称性的证明： *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

(** **** 练习：1 星, standard, optional (le_S_n)  *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (le_Sn_n_inf)  

    请提写出以下定理的非形式化证明：

    Theorem: For every [n], [~ (S n <= n)]

    此定理的形式化证明在下面作为可选的练习，
    不过在做形式化证明之前请先尝试写出非形式化的证明。

    证明： *)
    (* 请在此处解答 

    [] *)

(** **** 练习：1 星, standard, optional (le_Sn_n)  *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 在后面的章节中，我们主要会用到自反性和传递性。不过，
    我们先看一些其它的概念，作为在 Coq 中对关系进行操作的练习... *)

(* ----------------------------------------------------------------- *)
(** *** 对称关系与反对称关系 *)

(** 如果 [R a b] 蕴含 [R b a]，那么 [R] 就是_'对称关系'_。 *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** 练习：2 星, standard, optional (le_not_symmetric)  *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 如果 [R a b] 和 [R b a] 成立时有 [a = b]，那么 [R] 就是_'反对称关系'_。 *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** 练习：2 星, standard, optional (le_antisymmetric)  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (le_step)  *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 等价关系 *)

(** 如果一个关系满足自反性、对称性和传递性，那么它就是_'等价关系'_。 *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* ----------------------------------------------------------------- *)
(** *** 偏序关系与预序关系 *)

(** 如果某个关系满足自反性、_'反'_对称性和传递性，那么它就一个是_'偏序关系'_。
    在 Coq 标准库中，它被简短地称作“order”。 *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** 预序和偏序差不多，不过它无需满足反对称性。 *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.

(* ################################################################# *)
(** * 自反传递闭包 *)

(** 关系 [R] 的_'自反传递闭包'_是最小的包含 [R] 的自反传递关系。
    在 Coq 标准库的 Relations 模块中，此概念定义如下：*)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

(** 例如，[next_nat] 关系的自反传递闭包实际上就是 [le]。 *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

(** 以上对自反传递闭包的定义十分自然：它直接将自反传递闭包定义为“包含
    [R] 的，同时满足自反性和传递性的最小的关系”。
    然而此定义对于证明来说不是很方便，因为 [rt_trans] 的“非确定性”
    有时会让归纳变得很棘手。下面是最常用的定义： *)

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

(** 这一新的定义将 [rt_step] 和 [rt_trans] 合并成一条。在此规则的假设中
    [R] 只用了一次，这会让归纳法则更简单。

    在使用这一定义并继续之前，我们需要检查这两个定义确实定义了相同的关系...

    首先，我们来证明 [clos_refl_trans_1n] 模仿了两个“缺失”
    的 [clos_refl_trans] 构造子的行为。 *)

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

(** **** 练习：2 星, standard, optional (rsc_trans)  *)
Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 接着再用这些事实来证明这两个定义的自反性、
    传递性封闭确实定义了同样的关系。 *)

(** **** 练习：3 星, standard, optional (rtc_rsc_coincide)  *)
Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* Fri Jul 19 00:32:21 UTC 2019 *)
