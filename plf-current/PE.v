(** * PE: 部分求值 *)

(* 本章由單中杰（Chung-chieh Shan）撰写和维护。*)

(** [Equiv] 一章介绍了常量折叠作为程序变换的一个例子，并证明了此变换保持了程序的语义。
    常量折叠变换适用于明显的常量上，例如 [ANum] 表达式。比如说，它将命令 [Y ::= 3 + 1]
    化简为 [Y ::= 4]。然而它并不会顺着数据流传播已知的常量。例如，它无法化简如下的
    语句序列

      X ::= 3;; Y ::= X + 1

    为

      X ::= 3;; Y ::= 4

    因为当其运行到 [Y] 的时候并不知道 [X] 是 [3]。

    我们自然想要改进常量折叠，使其可以传播已知的常量并使用他们化简程序。
    这样做便得到了_'部分求值（partial evaluation）'_的初级形式。我们将会看到，
    部分求值之所以被这样形容是因为看起来它像在运行程序，但只有部分程序会被求值，
    因为程序只有一部分输入是已知的。比如，在不知道 [Y] 的初始值的情况下，我们仅能把

      X ::= 3;; Y ::= (X + 1) - Y

    化简到

      X ::= 3;; Y ::= 4 - Y
*)

From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

From PLF Require Import Smallstep.
From PLF Require Import Imp.

(* ################################################################# *)
(** * 一般化的常量折叠 *)

(** 作为开始，首先需要确定如何表达状态的部分事实。例如在上面的例子中，部分求值器会知道
    在两个赋值语句中间时 [X] 是 [3]，但不知道关于其他变量的任何信息。 *)

(* ================================================================= *)
(** ** 部分状态 *)

(** 从概念上讲，我们可以认为部分状态（partial state）的类型是 [string -> option nat]
    (相反全状态的类型是 [string -> nat]）。然而，除了对部分状态中的变量进行查询和更新以外，
    我们还想要比较两个部分状态，得到其不同的之处，并处理条件控制流。
    由于无法对两个任意的函数进行比较，因此我们更具体地把部分状态表示为由
    [string * nat] 序对构成的列表。*)

Definition pe_state := list (string * nat).

(** 一个（类型为 [string] 的）变量出现在列表中当且仅当我们知道其当前的 [nat] 值。
    [pe_lookup] 函数实现了这个功能的具体表示。（如果变量名在列表中出现了多次，
    那么我们仅使用第一个，但我们会定义部分求值器使其不会构造出这样的 [pe_state]。）*)

Fixpoint pe_lookup (pe_st : pe_state) (V:string) : option nat :=
  match pe_st with
  | [] => None
  | (V',n')::pe_st => if eqb_string V V' then Some n'
                      else pe_lookup pe_st V
  end.

(** 比如，[empty_pe_state] 表示空状态——一个将任何标识符都映射到 [None] 的函数。 *)

Definition empty_pe_state : pe_state := [].

(** 更一般地，如果这个 [list] 表示的 [pe_state] 不含有某个标识符，那么此 [pe_state]
    必将这个标识符映射到 [None]。在证明这一点之前，我们首先定义一个策略来帮助我们对
    字符串的等价关系进行推理。策略

      compare V V'

    用于对 [eqb_string V V'] 的分类情形进行推理。
    当 [V = V'] 时，此策略将全部的 [V] 替换为 [V']。 *)

Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
  destruct (eqb_stringP i j);
  [ subst j | ].

Theorem pe_domain: forall pe_st V n,
  pe_lookup pe_st V = Some n ->
  In V (map (@fst _ _) pe_st).
Proof. intros pe_st V n H. induction pe_st as [| [V' n'] pe_st].
  - (* [] *) inversion H.
  - (* :: *) simpl in H. simpl. compare V V'; auto. Qed.

(** 接下来，我们会大量使用标准库和 [Logic.v] 中定义的 [In] 性质： *)

Print In.
(* ===> Fixpoint In {A:Type} (a: A) (l:list A) : Prop :=
           match l with
           | [] => False
           | b :: m => b = a \/ In a m
            end
        : forall A : Type, A -> list A -> Prop *)

(** 除了我们之前学习过的关于 [In] 的众多引理，下面这个也会非常有用： *)

Check filter_In.
(* ===> filter_In : forall (A : Type) (f : A -> bool) (x : A) (l : list A),
            In x (filter f l) <-> In x l /\ f x = true  *)

(** 如果类型 [A] 有操作符 [eqb] 用于测试其元素的相等关系，我们可以计算一个布尔值 [inb eqb a l]
    用于测试 [In a l] 是否成立。 *)

Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) :=
  match l with
  | [] => false
  | a'::l' => eqb a a' || inb eqb a l'
  end.

(** 容易使用 [reflect] 性质关联起 [inb] 和 [In]： *)

Lemma inbP : forall A : Type, forall eqb : A->A->bool,
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
  intros A eqb beqP a l.
  induction l as [|a' l' IH].
  - constructor. intros [].
  - simpl. destruct (beqP a a').
    + subst. constructor. left. reflexivity.
    + simpl. destruct IH; constructor.
      * right. trivial.
      * intros [H1 | H2]; congruence.
Qed.

(* ================================================================= *)
(** ** 算术表达式 *)

(** 对 [aexp] 的部分求值是简单的——它基本上和常量折叠 [fold_constants_aexp] 相同，
    除了有时候部分状态可以告诉我们变量对应的值，我们便可以用一个常量替换这个变量。*)

Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => match pe_lookup pe_st i with (* <----- 新添加的 *)
             | Some n => ANum n
             | None => AId i
             end
  | APlus a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

(** 部分求值器会折叠起常量，但并不会应用加法的结合律。 *)

Example test_pe_aexp1:
  pe_aexp [(X,3)] (X + 1 + Y)%imp
  = (4 + Y)%imp.
Proof. reflexivity. Qed.

Example text_pe_aexp2:
  pe_aexp [(Y,3)] (X + 1 + Y)%imp
  = (X + 1 + 3)%imp.
Proof. reflexivity. Qed.

(** 现在，[pe_aexp] 在什么意义上是正确的呢？可以合理地将 [pe_aexp] 的正确性
    定义为：若一个全状态 [st:state] 与部分状态 [pe_st:pe_state] 是相容的
    （换句话说，[pe_st] 中每个变量的值同 [st] 中这个变量的值相同），那么在 [st]
    状态中对 [a] 求值和对 [pe_aexp pe_st a] 求值会产生相同结果。这个陈述确实是真的。*)

Definition pe_consistent (st:state) (pe_st:pe_state) :=
  forall V n, Some n = pe_lookup pe_st V -> st V = n.

Theorem pe_aexp_correct_weak: forall st pe_st, pe_consistent st pe_st ->
  forall a, aeval st a = aeval st (pe_aexp pe_st a).
Proof. unfold pe_consistent. intros st pe_st H a.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  (* 同 fold_constants_aexp_sound 比较，唯一不同的分类是 AId。 *)
  - (* AId *)
    remember (pe_lookup pe_st x) as l. destruct l.
    + (* Some *) rewrite H with (n:=n) by apply Heql. reflexivity.
    + (* None *) reflexivity.
Qed.

(** 然而，我们很快就会希望这个部分求值器可以移除掉赋值语句。比如说，它会将

    X ::= 3;; Y ::= X - Y;; X ::= 4

    简化为

    Y ::= 3 - Y;; X ::= 4

    它保留了最后对 [X] 的赋值语句。为了完成这种简化，我们需要部分求值的结果

    pe_aexp [(X,3)] (X - Y)

    等于 [3 - Y] 而_非_原始的表达式 [X -Y]。毕竟，若将

    X ::= 3;; Y ::= X - Y;; X ::= 4

    变换为

    Y ::= X - Y;; X ::= 4

    就不仅仅是低效的，而是不正确的结果了，尽管结果表达式 [3 - Y] 和 [X - Y]
    都满足我们上面证明的正确性条件。确实，如果我们只是定义 [pe_aexp pt_st a = a]
    那么定理 [pe_aexp_correct_weak] 也会直接成立。

    但是，我们想要证明关于 [pe_aexp] 更强的正确性：对部分求值产生的表达式进行求值
    （[aeval st (pe_aexp pe_st a)]） 必须不依赖全状态 [st] 中已经被部分状态
    [pe_st] 所指明的部分。为了精确地表达，让我们定义一个函数 [pe_override]，
    它使用 [pe_st] 中的内容更新 [st]。换句话说，[pe_override] 将 [pe_st]
    中的赋值语句置于 [st] 之上。 *)

Fixpoint pe_update (st:state) (pe_st:pe_state) : state :=
  match pe_st with
  | [] => st
  | (V,n)::pe_st => t_update (pe_update st pe_st) V n
  end.

Example test_pe_update:
  pe_update (Y !-> 1) [(X,3);(Z,2)]
  = (X !-> 3 ; Z !-> 2 ; Y !-> 1).
Proof. reflexivity. Qed.

(** 尽管 [pe_update] 对一个具体的 [list] 表示的 [pe_state] 进行操作，它的行为完全
    由 [pe_lookup] 对 [pe_state] 的解释所定义。 *)

Theorem pe_update_correct: forall st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | Some n => n
  | None => st V0
  end.
Proof. intros. induction pe_st as [| [V n] pe_st]. reflexivity.
  simpl in *. unfold t_update.
  compare V0 V; auto. rewrite <- eqb_string_refl; auto. rewrite false_eqb_string; auto. Qed.

(** 我们可以以两种方式关联起 [pe_consistent] 和 [pe_update]。
    首先，用部分状态覆写一个状态总是会得到同这个部分状态相容的状态。
    第二，如果一个状态本身同某个部分状态相容，那么用这个部分状态覆写
    这个状态会得到相同的状态。*)

Theorem pe_update_consistent: forall st pe_st,
  pe_consistent (pe_update st pe_st) pe_st.
Proof. intros st pe_st V n H. rewrite pe_update_correct.
  destruct (pe_lookup pe_st V); inversion H. reflexivity. Qed.

Theorem pe_consistent_update: forall st pe_st,
  pe_consistent st pe_st -> forall V, st V = pe_update st pe_st V.
Proof. intros st pe_st H V. rewrite pe_update_correct.
  remember (pe_lookup pe_st V) as l. destruct l; auto. Qed.

(** 现在我们可以表述和证明 [pe_aexp] 更强的正确性，这会帮助我们定义接下来的部分求值器。

    直观地讲，使用部分求值来运行程序由两个阶段构成。第一个为_'静态'_阶段（static stage），
    我们在部分状态下对程序进行部分求值，并得到一个_'剩余'_程序（residual program）。
    第二个为_'动态'_阶段（dynamic stage），我们在动态状态中对剩余程序进行求值。
    这个动态状态提供了在静态（部分）状态中未知的变量的值。因此，剩余程序应当等价于
    对原始程序_'预添加（prepending）'_上部分状态中的赋值语句。 *)

Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a).
Proof.
  intros pe_st a st.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  (* 同 fold_constants_aexp_sound 比较，唯一不同的分类是 AId。 *)
  rewrite pe_update_correct. destruct (pe_lookup pe_st x); reflexivity.
Qed.

(* ================================================================= *)
(** ** 布尔表达式 *)

(** 对布尔表达式的部分求值是相似的。事实上，它完全类似于对布尔表达式常量折叠，
    因为我们的语言中并没有布尔值的变量。 *)

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 =? n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1 =>
      match (pe_bexp pe_st b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example test_pe_bexp1:
  pe_bexp [(X,3)] (~(X <= 3))%imp
  = false.
Proof. reflexivity. Qed.

Example test_pe_bexp2: forall b:bexp,
  b = (~(X <= (X + 1)))%imp ->
  pe_bexp [] b = b.
Proof. intros b H. rewrite -> H. reflexivity. Qed.

(** [pe_bexp] 的正确性和上面 [pe_aexp] 的正确性类似。 *)

Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b).
Proof.
  intros pe_st b st.
  induction b; simpl;
    try reflexivity;
    try (remember (pe_aexp pe_st a1) as a1';
         remember (pe_aexp pe_st a2) as a2';
         assert (H1: aeval (pe_update st pe_st) a1 = aeval st a1');
         assert (H2: aeval (pe_update st pe_st) a2 = aeval st a2');
           try (subst; apply pe_aexp_correct);
         destruct a1'; destruct a2'; rewrite H1; rewrite H2;
         simpl; try destruct (n =? n0);
         try destruct (n <=? n0); reflexivity);
    try (destruct (pe_bexp pe_st b); rewrite IHb; reflexivity);
    try (destruct (pe_bexp pe_st b1);
         destruct (pe_bexp pe_st b2);
         rewrite IHb1; rewrite IHb2; reflexivity).
Qed.

(* ################################################################# *)
(** * 无循环命令的部分求值 *)

(** 接下来如何处理对命令的部分求值呢？部分求值和完全求值之间的类比仍然适用：
    对命令的完全求值将初始状态转换为最终的状态，而对命令的部分求值将初始状态转换为
    最终的部分状态。不过，由于状态是局部的，一些命令可能无法在静态阶段执行。
    因此，正如同 [pe_aexp] 返回一个 [aexp] 的剩余表达式、[pe_bexp] 返回一个
    [bexp] 的剩余表达式，对命令的部分求值也产生剩余命令。

    另一个部分求值和完全求值相似的地方是它不会对所有命令都停机。构造出一个
    部分求值器使其对所有的命令都停机并不是困难的；困难在于所构造的部分求值器
    在停机的同时还能自动地执行想要的优化，例如循环展开。如果我们有意把
    源程序以一种更容易区分出静态阶段和动态阶段的方式写出，那么部分求值器
    常常可以停机并执行更多优化。这种方式被称作_'绑定时间改进（binding-time
    improvement）'_。变量的绑定时间告诉我们何时可以知道它的值——“静态”或“动态”。

    不管怎样，我们现在先接受这样的事实，即这个部分求值器不会是一个从源程序
    和初始状态到剩余程序和最终部分状态的全函数。为了对这种非停机性建模，我们
    采用和命令的完全求值相同的技术，即归纳地定义关系。我们写下

      c1 / st \\ c1' / st'

    意思是对源程序 [c1] 在初始状态 [st] 中部分求值产生剩余程序 [c1']
    和最终部分状态 [st']。举个例子，我们想要让

      [] / (X ::= 3 ;; Y ::= Z * (X + X)) \\ (Y ::= Z * 6) / [(X,3)]

    成立。对 [X] 的赋值出现在最终部分状态中，而非剩余命令中。

    （写成 [st =[ c1 ]=> c1' / st'] 的形式会更接近于 [Imp] 使用的记法，
    或许这里需要改一下！）
*)

(* ================================================================= *)
(** ** 赋值 *)

(** 让我们首先考虑对赋值语句的部分求值。上面源程序中的两个赋值语句需要区别对待。
    第一个赋值 [X ::= 3] 是_'静态的'_：它的右值是一个常量（更一般地讲，可以
    简化为常量），因此我们需要更新部分状态中的 [X] 为 [3]，而不产生剩余代码。
    （实际上，我们产生了剩余程序 [SKIP]。）第二个赋值 [Y ::= Z * (X + X)]
    是_'动态的'_：它的右值无法被简化为常量，因此我们应当将它保留在剩余程序
    中，并且若 [Y] 出现在部分状态中，则应当被移除。为了实现这两个情形，我们定
    义函数 [pe_add] 和 [pe_remove]。与 [pe_update] 类似，这些函数操作
    某个具体的 [list] 表示的 [pe_state]，但定理 [pe_add_correct] 和
    [pe_remove_correct] 通过 [pe_lookup] 对 [pe_state] 的解释定义了
    他们的行为。 *)

Fixpoint pe_remove (pe_st:pe_state) (V:string) : pe_state :=
  match pe_st with
  | [] => []
  | (V',n')::pe_st => if eqb_string V V' then pe_remove pe_st V
                      else (V',n') :: pe_remove pe_st V
  end.

Theorem pe_remove_correct: forall pe_st V V0,
  pe_lookup (pe_remove pe_st V) V0
  = if eqb_string V V0 then None else pe_lookup pe_st V0.
Proof. intros pe_st V V0. induction pe_st as [| [V' n'] pe_st].
  - (* [] *) destruct (eqb_string V V0); reflexivity.
  - (* :: *) simpl. compare V V'.
    + (* 相等 *) rewrite IHpe_st.
      destruct (eqb_stringP V V0).  reflexivity.
      rewrite false_eqb_string; auto.
    + (* 不相等 *) simpl. compare V0 V'.
      * (* 相等 *) rewrite false_eqb_string; auto.
      * (* 不相等 *) rewrite IHpe_st. reflexivity.
Qed.

Definition pe_add (pe_st:pe_state) (V:string) (n:nat) : pe_state :=
  (V,n) :: pe_remove pe_st V.

Theorem pe_add_correct: forall pe_st V n V0,
  pe_lookup (pe_add pe_st V n) V0
  = if eqb_string V V0 then Some n else pe_lookup pe_st V0.
Proof. intros pe_st V n V0. unfold pe_add. simpl.
  compare V V0.
  - (* 相等 *) rewrite <- eqb_string_refl; auto.
  - (* 不相等 *) rewrite pe_remove_correct.
    repeat rewrite false_eqb_string; auto.
Qed.

(** 我们将会用下面的两个定理证明部分求值器正确地处理了动态赋值和静态赋值。*)

Theorem pe_update_update_remove: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update (t_update st V n) (pe_remove pe_st V).
Proof. intros st pe_st V n. apply functional_extensionality.
  intros V0. unfold t_update. rewrite !pe_update_correct.
  rewrite pe_remove_correct. destruct (eqb_string V V0); reflexivity.
  Qed.

Theorem pe_update_update_add: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update st (pe_add pe_st V n).
Proof. intros st pe_st V n. apply functional_extensionality. intros V0.
  unfold t_update. rewrite !pe_update_correct. rewrite pe_add_correct.
  destruct (eqb_string V V0); reflexivity. Qed.

(* ================================================================= *)
(** ** 条件 *)

(** 比赋值语句的部分求值要麻烦一点的是条件语句 [TEST b1 THEN c1 ELSE c2 FI]。
    如果 [b1] 被简化为 [BTrue] 或 [BFalse]，那么会很容易：我们知道哪个分支
    会被运行。如果 [b1] 不会被简化为常量，那么我们需要对两个分支部分地求值，
    且最终的部分状态在两个分支上可能是不同的！

    下面的程序展示了这种困难：

      X ::= 3;;
      TEST Y <= 4 THEN
          Y ::= 4;;
          TEST X <= Y THEN Y ::= 999 ELSE SKIP FI
      ELSE SKIP FI

    假设初始的部分状态为空状态。静态来说，我们不知道 [Y] 和 [4] 比较的结果，
    因此必须对（外层的）条件语句的两个分支都进行部分求值。在其 [THEN]
    分支中，我们知道 [Y] 被赋值为 [4]，并且可以利用这一点来化简一部分代码。
    在 [ELSE] 分支中，到最后我们仍然不知道 [Y] 的值会是什么。最终部分状态
    和剩余程序应该是什么呢？

    一种处理动态的条件语句的方法是取两个分支上最终部分状态的交。在上面的例子中，
    我们取 [(Y,4),(X,3)] 和 [(X,3)] 的交，因此最终的部分状态为 [(X,3)]。
    为了抵消丢失掉的对 [Y] 的赋值 [4]，我们需要在 [THEN] 分支的最后添加赋值语句
    [Y ::= 4]。因此，剩余程序为

      SKIP;;
      TEST Y <= 4 THEN
          SKIP;;
          SKIP;;
          Y ::= 4
      ELSE SKIP FI

    在 Coq 中编程处理这种情况需要几个辅助函数：我们需要计算两个 [pe_state]
    的交（intersection），并将他们的差（difference）转换为一系列的赋值语句。

    首先，我们展示如何计算两个 [pe_state] 是否对某个变量有不同的值。定理
    [pe_disagree_domain] 证明了两个 [pe_state] 若对某个变量有不同的值，
    那么此变量必在至少一个状态中出现。 *)

Definition pe_disagree_at (pe_st1 pe_st2 : pe_state) (V:string) : bool :=
  match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
  | Some x, Some y => negb (x =? y)
  | None, None => false
  | _, _ => true
  end.

Theorem pe_disagree_domain: forall (pe_st1 pe_st2 : pe_state) (V:string),
  true = pe_disagree_at pe_st1 pe_st2 V ->
  In V (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2).
Proof. unfold pe_disagree_at. intros pe_st1 pe_st2 V H.
  apply in_app_iff.
  remember (pe_lookup pe_st1 V) as lookup1.
  destruct lookup1 as [n1|]. left.  apply pe_domain with n1. auto.
  remember (pe_lookup pe_st2 V) as lookup2.
  destruct lookup2 as [n2|]. right. apply pe_domain with n2. auto.
  inversion H. Qed.

(** 给定两个 [pe_state]，我们定义函数 [pe_compare] 用于列出在他们中值不同的变量。
    根据 [pe_compare_correct]，列出的变量是精确的：一个变量在列表中当且仅当给定
    的两个 [pe_state] 对其有不同的值。进一步地，我们用 [pe_unique] 函数来消除
    列表中的重复。*)

Fixpoint pe_unique (l : list string) : list string :=
  match l with
  | [] => []
  | x::l =>
      x :: filter (fun y => if eqb_string x y then false else true) (pe_unique l)
  end.

Theorem pe_unique_correct: forall l x,
  In x l <-> In x (pe_unique l).
Proof. intros l x. induction l as [| h t]. reflexivity.
  simpl in *. split.
  - (* -> *)
    intros. inversion H; clear H.
      left. assumption.
      destruct (eqb_stringP h x).
         left.  assumption.
         right.  apply filter_In. split.
           apply IHt. assumption.
           rewrite false_eqb_string; auto.
  - (* <- *)
    intros. inversion H; clear H.
       left. assumption.
       apply filter_In in H0.  inversion H0. right. apply IHt. assumption.
Qed.

Definition pe_compare (pe_st1 pe_st2 : pe_state) : list string :=
  pe_unique (filter (pe_disagree_at pe_st1 pe_st2)
    (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2)).

Theorem pe_compare_correct: forall pe_st1 pe_st2 V,
  pe_lookup pe_st1 V = pe_lookup pe_st2 V <->
  ~ In V (pe_compare pe_st1 pe_st2).
Proof. intros pe_st1 pe_st2 V.
  unfold pe_compare. rewrite <- pe_unique_correct. rewrite filter_In.
  split; intros Heq.
  - (* -> *)
    intro. destruct H. unfold pe_disagree_at in H0. rewrite Heq in H0.
    destruct (pe_lookup pe_st2 V).
    rewrite <- beq_nat_refl in H0. inversion H0.
    inversion H0.
  - (* <- *)
    assert (Hagree: pe_disagree_at pe_st1 pe_st2 V = false).
    { (* 对断言的证明 *)
      remember (pe_disagree_at pe_st1 pe_st2 V) as disagree.
      destruct disagree; [| reflexivity].
      apply  pe_disagree_domain in Heqdisagree.
      exfalso. apply Heq. split. assumption. reflexivity. }
    unfold pe_disagree_at in Hagree.
    destruct (pe_lookup pe_st1 V) as [n1|];
    destruct (pe_lookup pe_st2 V) as [n2|];
      try reflexivity; try solve_by_invert.
    rewrite negb_false_iff in Hagree.
    apply eqb_eq in Hagree. subst. reflexivity. Qed.

(** 两个部分状态的交是从其中一个状态中移除所有值不同的变量。我们用上面的
    [pe_remove] 来定义函数 [pe_removes]，用于一次性地移除一个列表中的变量。

    定理 [pe_compare_removes] 证明了无论我们从哪个状态中移除变量，最终得到
    的交在 [pe_lookup] 的解释下都是相同的。因为 [pe_update] 仅依赖 [pe_lookup]
    对部分状态的解释，我们选择从哪个状态中移除变量也不会影响到 [pe_update]；
    后面的正确性证明中会用到 [pe_compare_update] 定理。*)

Fixpoint pe_removes (pe_st:pe_state) (ids : list string) : pe_state :=
  match ids with
  | [] => pe_st
  | V::ids => pe_remove (pe_removes pe_st ids) V
  end.

Theorem pe_removes_correct: forall pe_st ids V,
  pe_lookup (pe_removes pe_st ids) V =
  if inb eqb_string V ids then None else pe_lookup pe_st V.
Proof. intros pe_st ids V. induction ids as [| V' ids]. reflexivity.
  simpl. rewrite pe_remove_correct. rewrite IHids.
  compare V' V.
  - rewrite <- eqb_string_refl. reflexivity.
  - rewrite false_eqb_string; try congruence. reflexivity.
Qed.

Theorem pe_compare_removes: forall pe_st1 pe_st2 V,
  pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
  pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V.
Proof.
  intros pe_st1 pe_st2 V. rewrite !pe_removes_correct.
  destruct (inbP _ _ eqb_stringP V (pe_compare pe_st1 pe_st2)).
  - reflexivity.
  - apply pe_compare_correct. auto. Qed.

Theorem pe_compare_update: forall pe_st1 pe_st2 st,
  pe_update st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
  pe_update st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)).
Proof. intros. apply functional_extensionality. intros V.
  rewrite !pe_update_correct. rewrite pe_compare_removes. reflexivity.
Qed.

(** 最后，我们定义 [assign] 函数将两个部分状态的差转换为一系列的赋值命令。
    准确地说，[assign pe_st ids] 对 [ids] 中的每个变量生成一个赋值命令。*)

Fixpoint assign (pe_st : pe_state) (ids : list string) : com :=
  match ids with
  | [] => SKIP
  | V::ids => match pe_lookup pe_st V with
              | Some n => (assign pe_st ids;; V ::= ANum n)
              | None => assign pe_st ids
              end
  end.

(** 由 [assign] 生成的命令总是会停机，因为他们仅仅是赋值命令而已。下面的（全）函数
    [assigned] 计算了命令在动态状态上的作用。定理 [assign_removes] 进一步确认了
    生成的赋值语句抵消了部分状态中所移除的变量。*)

Definition assigned (pe_st:pe_state) (ids : list string) (st:state) : state :=
  fun V => if inb eqb_string V ids then
                match pe_lookup pe_st V with
                | Some n => n
                | None => st V
                end
           else st V.

Theorem assign_removes: forall pe_st ids st,
  pe_update st pe_st =
  pe_update (assigned pe_st ids st) (pe_removes pe_st ids).
Proof. intros pe_st ids st. apply functional_extensionality. intros V.
  rewrite !pe_update_correct. rewrite pe_removes_correct. unfold assigned.
  destruct (inbP _ _ eqb_stringP V ids); destruct (pe_lookup pe_st V); reflexivity.
Qed.

Lemma ceval_extensionality: forall c st st1 st2,
  st =[ c ]=> st1 -> (forall V, st1 V = st2 V) -> st =[ c ]=> st2.
Proof. intros c st st1 st2 H Heq.
  apply functional_extensionality in Heq. rewrite <- Heq. apply H. Qed.

Theorem eval_assign: forall pe_st ids st,
  st =[ assign pe_st ids ]=> assigned pe_st ids st.
Proof. intros pe_st ids st. induction ids as [| V ids]; simpl.
  - (* [] *) eapply ceval_extensionality. apply E_Skip. reflexivity.
  - (* V::ids *)
    remember (pe_lookup pe_st V) as lookup. destruct lookup.
    + (* Some *) eapply E_Seq. apply IHids. unfold assigned. simpl.
      eapply ceval_extensionality. apply E_Ass. simpl. reflexivity.
      intros V0. unfold t_update.  compare V V0.
      * (* 相等 *) rewrite <- Heqlookup. rewrite <- eqb_string_refl. reflexivity.
      * (* 不相等 *) rewrite false_eqb_string; simpl; congruence.
    + (* None *) eapply ceval_extensionality. apply IHids.
      unfold assigned. intros V0. simpl. compare V V0.
      * (* 相等 *) rewrite <- Heqlookup.
        rewrite <- eqb_string_refl.
        destruct (inbP _ _ eqb_stringP V ids); reflexivity.
      * (* 不相等 *) rewrite false_eqb_string; simpl; congruence.
Qed.

(* ================================================================= *)
(** ** 部分求值关系 *)

(** 终于，我们可以将无循环命令的部分求值器定义为一个归纳关系了！
    [PE_AssDynamic] 和 [PE_If] 中的不等式仅仅是为了使部分求值器
    保持确定性；他们并不是正确性所需要的。*)

Reserved Notation "c1 '/' st '\\' c1' '/' st'"
  (at level 40, st at level 39, c1' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> Prop :=
  | PE_Skip : forall pe_st,
      SKIP / pe_st \\ SKIP / pe_st
  | PE_AssStatic : forall pe_st a1 n1 l,
      pe_aexp pe_st a1 = ANum n1 ->
      (l ::= a1) / pe_st \\ SKIP / pe_add pe_st l n1
  | PE_AssDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n, a1' <> ANum n) ->
      (l ::= a1) / pe_st \\ (l ::= a1') / pe_remove pe_st l
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2',
      c1 / pe_st  \\ c1' / pe_st' ->
      c2 / pe_st' \\ c2' / pe_st'' ->
      (c1 ;; c2) / pe_st \\ (c1' ;; c2') / pe_st''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c1' / pe_st'
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2',
      pe_bexp pe_st b1 = BFalse ->
      c2 / pe_st \\ c2' / pe_st' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c2' / pe_st'
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
      pe_bexp pe_st b1 <> BTrue ->
      pe_bexp pe_st b1 <> BFalse ->
      c1 / pe_st \\ c1' / pe_st1 ->
      c2 / pe_st \\ c2' / pe_st2 ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st
        \\ (TEST pe_bexp pe_st b1
             THEN c1' ;; assign pe_st1 (pe_compare pe_st1 pe_st2)
             ELSE c2' ;; assign pe_st2 (pe_compare pe_st1 pe_st2) FI)
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)

  where "c1 '/' st '\\' c1' '/' st'" := (pe_com c1 st c1' st').

Hint Constructors pe_com.
Hint Constructors ceval.

(* ================================================================= *)
(** ** 例子 *)

(** 下面给出一些使用部分求值器的例子。为了使 [pe_com] 关系可以自动化地完成
    部分求值，我们会需要在 Coq 中定义一些自动化的策略。这不会十分困难，
    但这里并不是必须的。 *)

Example pe_example1:
  (X ::= 3 ;; Y ::= Z * (X + X))%imp
  / [] \\ (SKIP;; Y ::= Z * 6)%imp / [(X,3)].
Proof. eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  eapply PE_AssDynamic. reflexivity. intros n H. inversion H. Qed.

Example pe_example2:
  (X ::= 3 ;; TEST X <= 4 THEN X ::= 4 ELSE SKIP FI)%imp
  / [] \\ (SKIP;; SKIP)%imp / [(X,4)].
Proof. eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  eapply PE_IfTrue. reflexivity.
  eapply PE_AssStatic. reflexivity. Qed.

Example pe_example3:
  (X ::= 3;;
   TEST Y <= 4 THEN
     Y ::= 4;;
     TEST X = Y THEN Y ::= 999 ELSE SKIP FI
   ELSE SKIP FI)%imp / []
  \\ (SKIP;;
       TEST Y <= 4 THEN
         (SKIP;; SKIP);; (SKIP;; Y ::= 4)
       ELSE SKIP;; SKIP FI)%imp
      / [(X,3)].
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  eapply PE_If; intuition eauto; try solve_by_invert.
  econstructor. eapply PE_AssStatic. reflexivity.
  eapply PE_IfFalse. reflexivity. econstructor.
  reflexivity. reflexivity. Qed.

(* ================================================================= *)
(** ** 部分求值的正确性 *)

(** 最后，让我们来证明这个部分求值器是正确的！ *)

Reserved Notation "c' '/' pe_st' '/' st '\\' st''"
  (at level 40, pe_st' at level 39, st at level 39).

Inductive pe_ceval
  (c':com) (pe_st':pe_state) (st:state) (st'':state) : Prop :=
  | pe_ceval_intro : forall st',
    st =[ c' ]=> st' ->
    pe_update st' pe_st' = st'' ->
    c' / pe_st' / st \\ st''
  where "c' '/' pe_st' '/' st '\\' st''" := (pe_ceval c' pe_st' st st'').

Hint Constructors pe_ceval.

Theorem pe_com_complete:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') ->
  (c' / pe_st' / st \\ st'').
Proof. intros c pe_st pe_st' c' Hpe.
  induction Hpe; intros st st'' Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - (* PE_AssStatic *) econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. reflexivity.
  - (* PE_AssDynamic *) econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    reflexivity.
  - (* PE_Seq *)
    edestruct IHHpe1. eassumption. subst.
    edestruct IHHpe2. eassumption.
    eauto.
  - (* PE_If *) inversion Heval; subst.
    + (* E'IfTrue *) edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption.
    + (* E_IfFalse *) edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption.
Qed.

Theorem pe_com_sound:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' ->
  forall st st'',
  (c' / pe_st' / st \\ st'') ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' Hpe.
  induction Hpe;
    intros st st'' [st' Heval Heq];
    try (inversion Heval; []; subst); auto.
  - (* PE_AssStatic *) rewrite <- pe_update_update_add. apply E_Ass.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - (* PE_AssDynamic *) rewrite <- pe_update_update_remove. apply E_Ass.
    rewrite <- pe_aexp_correct. reflexivity.
  - (* PE_Seq *) eapply E_Seq; eauto.
  - (* PE_IfTrue *) apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
  - (* PE_IfFalse *) apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
  - (* PE_If *)
    inversion Heval; subst; inversion H7;
      (eapply ceval_deterministic in H8; [| apply eval_assign]); subst.
    + (* E_IfTrue *)
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      rewrite <- assign_removes. eauto.
    + (* E_IfFalse *)
      rewrite -> pe_compare_update.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      rewrite <- assign_removes. eauto.
Qed.

(** 最终的主定理。感谢 David Menendez 所贡献的这个公式！ *)

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (c' / pe_st' / st \\ st'').
Proof. intros c pe_st pe_st' c' H st st''. split.
  - (* -> *) apply pe_com_complete. apply H.
  - (* <- *) apply pe_com_sound. apply H.
Qed.

(* ################################################################# *)
(** * 循环的部分求值 *)

(** 初看上去，将部分求值关系 [pe_com] 扩展到循环是简单直接的。确实，很多循环程序
    是容易处理的。比如说，考虑下面重复计算平方的循环：

      WHILE 1 <= X DO
          Y ::= Y * Y;;
          X ::= X - 1
      END

    如果我们不知道 [X] 或 [Y] 的静态值，那么整个循环是动态的，其剩余程序与源程序相同。
    如果我们知道 [X] 但不知道 [Y]，那么循环可以被展开，最后的剩余程序可能是

      Y ::= Y * Y;;
      Y ::= Y * Y;;
      Y ::= Y * Y

    当 [X] 初始为 [3] 时（最终变为 [0]）。一般来说，如果循环体的最终部分状态和初始状态
    相同，或者其条件是静态的，那么对循环的部分求值很容易。

    但是其他的循环程序则很难在 Imp 中表达出我们期待的剩余程序。举个例子，下面的程序检查
    [Y] 是奇数还是偶数：

      X ::= 0;;
      WHILE 1 <= Y DO
          Y ::= Y - 1 ;;
          X ::= 1 - X
      END

    [X] 的值在循环过程中交替地为 [0] 或 [1]。理想情况，我们想要展开循环两次，
    而非不加限制地，并得到类似如下程序

      WHILE 1 <= Y DO
          Y ::= Y - 1;;
          IF 1 <= Y THEN
              Y ::= Y - 1
          ELSE
              X ::= 1;; EXIT
          FI
      END;;
      X ::= 0

    不幸地是，Imp 中并没有 [EXIT] 命令。在不对语言扩展控制结构的情况，我们能采取的
    最好方法是是重复循环条件或添加标记变量。不论哪种都不是非常有吸引力。

    作为一个题外话，下面是一个对 Imp 命令进行部分求值的尝试。我们对 [pe_com]
    关系添加一个新的命令参数 [c'']，用于记录循环的累积。*)

Module Loop.

Reserved Notation "c1 '/' st '\\' c1' '/' st' '/' c''"
  (at level 40, st at level 39, c1' at level 39, st' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> com -> Prop :=
  | PE_Skip : forall pe_st,
      SKIP / pe_st \\ SKIP / pe_st / SKIP
  | PE_AssStatic : forall pe_st a1 n1 l,
      pe_aexp pe_st a1 = ANum n1 ->
      (l ::= a1) / pe_st \\ SKIP / pe_add pe_st l n1 / SKIP
  | PE_AssDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n, a1' <> ANum n) ->
      (l ::= a1) / pe_st \\ (l ::= a1') / pe_remove pe_st l / SKIP
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
      c1 / pe_st  \\ c1' / pe_st' / SKIP ->
      c2 / pe_st' \\ c2' / pe_st'' / c'' ->
      (c1 ;; c2) / pe_st \\ (c1' ;; c2') / pe_st'' / c''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1' c'',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' / c'' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c1' / pe_st' / c''
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2' c'',
      pe_bexp pe_st b1 = BFalse ->
      c2 / pe_st \\ c2' / pe_st' / c'' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c2' / pe_st' / c''
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
      pe_bexp pe_st b1 <> BTrue ->
      pe_bexp pe_st b1 <> BFalse ->
      c1 / pe_st \\ c1' / pe_st1 / c'' ->
      c2 / pe_st \\ c2' / pe_st2 / c'' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st
        \\ (TEST pe_bexp pe_st b1
             THEN c1' ;; assign pe_st1 (pe_compare pe_st1 pe_st2)
             ELSE c2' ;; assign pe_st2 (pe_compare pe_st1 pe_st2) FI)
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)
            / c''
  | PE_WhileFalse : forall pe_st b1 c1,
      pe_bexp pe_st b1 = BFalse ->
      (WHILE b1 DO c1 END) / pe_st \\ SKIP / pe_st / SKIP
  | PE_WhileTrue : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st' \\ c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (WHILE b1 DO c1 END) / pe_st \\ (c1';;c2') / pe_st'' / c2''
  | PE_While : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 <> BFalse ->
      pe_bexp pe_st b1 <> BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st' \\ c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (c2'' = SKIP%imp \/ c2'' = WHILE b1 DO c1 END%imp) ->
      (WHILE b1 DO c1 END) / pe_st
        \\ (TEST pe_bexp pe_st b1
             THEN c1';; c2';; assign pe_st'' (pe_compare pe_st pe_st'')
             ELSE assign pe_st (pe_compare pe_st pe_st'') FI)%imp
            / pe_removes pe_st (pe_compare pe_st pe_st'')
            / c2''
  | PE_WhileFixedEnd : forall pe_st b1 c1,
      pe_bexp pe_st b1 <> BFalse ->
      (WHILE b1 DO c1 END) / pe_st \\ SKIP / pe_st / (WHILE b1 DO c1 END)
  | PE_WhileFixedLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st'
        \\ c2' / pe_st'' / (WHILE b1 DO c1 END) ->
      pe_compare pe_st pe_st'' = [] ->
      (WHILE b1 DO c1 END) / pe_st
        \\ (WHILE BTrue DO SKIP END) / pe_st / SKIP
      (* 因为这里是一个无限循环，我们实际上应该开始抛弃剩下的程序：
         (WHILE b1 DO c1 END) / pe_st
         \\ SKIP / pe_st / (WHILE BTrue DO SKIP END) *)
  | PE_WhileFixed : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 <> BFalse ->
      pe_bexp pe_st b1 <> BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st'
        \\ c2' / pe_st'' / (WHILE b1 DO c1 END) ->
      pe_compare pe_st pe_st'' = [] ->
      (WHILE b1 DO c1 END) / pe_st
        \\ (WHILE pe_bexp pe_st b1 DO c1';; c2' END) / pe_st / SKIP

  where "c1 '/' st '\\' c1' '/' st' '/' c''" := (pe_com c1 st c1' st' c'').

Hint Constructors pe_com.

(* ================================================================= *)
(** ** 例子 *)

Ltac step i :=
  (eapply i; intuition eauto; try solve_by_invert);
  repeat (try eapply PE_Seq;
          try (eapply PE_AssStatic; simpl; reflexivity);
          try (eapply PE_AssDynamic;
               [ simpl; reflexivity
               | intuition eauto; solve_by_invert])).

Definition square_loop: com :=
  (WHILE 1 <= X DO
    Y ::= Y * Y;;
    X ::= X - 1
  END)%imp.

Example pe_loop_example1:
  square_loop / []
  \\ (WHILE 1 <= X DO
         (Y ::= Y * Y;;
          X ::= X - 1);; SKIP
       END)%imp / [] / SKIP.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  step PE_WhileFixed. step PE_WhileFixedEnd. reflexivity.
  reflexivity. reflexivity. Qed.

Example pe_loop_example2:
  (X ::= 3;; square_loop)%imp / []
  \\ (SKIP;;
       (Y ::= Y * Y;; SKIP);;
       (Y ::= Y * Y;; SKIP);;
       (Y ::= Y * Y;; SKIP);;
       SKIP)%imp / [(X,0)] / SKIP%imp.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  step PE_WhileTrue.
  step PE_WhileTrue.
  step PE_WhileTrue.
  step PE_WhileFalse.
  inversion H. inversion H. inversion H.
  reflexivity. reflexivity. Qed.

Example pe_loop_example3:
  (Z ::= 3;; subtract_slowly) / []
  \\ (SKIP;;
       TEST ~(X = 0) THEN
         (SKIP;; X ::= X - 1);;
         TEST ~(X = 0) THEN
           (SKIP;; X ::= X - 1);;
           TEST ~(X = 0) THEN
             (SKIP;; X ::= X - 1);;
             WHILE ~(X = 0) DO
               (SKIP;; X ::= X - 1);; SKIP
             END;;
             SKIP;; Z ::= 0
           ELSE SKIP;; Z ::= 1 FI;; SKIP
         ELSE SKIP;; Z ::= 2 FI;; SKIP
       ELSE SKIP;; Z ::= 3 FI)%imp / [] / SKIP.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  step PE_While.
  step PE_While.
  step PE_While.
  step PE_WhileFixed.
  step PE_WhileFixedEnd.
  reflexivity. inversion H. inversion H. inversion H.
  reflexivity. reflexivity. Qed.

Example pe_loop_example4:
  (X ::= 0;;
   WHILE X <= 2 DO
     X ::= 1 - X
   END)%imp / [] \\ (SKIP;; WHILE true DO SKIP END)%imp / [(X,0)] / SKIP.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  step PE_WhileFixedLoop.
  step PE_WhileTrue.
  step PE_WhileFixedEnd.
  inversion H. reflexivity. reflexivity. reflexivity. Qed.

(* ================================================================= *)
(** ** 正确性 *)

(** 由于部分求值器可以展开一个循环 n 次，其中 n 是一个大于一的有限整数，为了证明其
    正确性我们需要对循环体动态求值的次数进行归纳，而非结构地对动态求值归纳。*)

Reserved Notation "c1 '/' st '\\' st' '#' n"
  (at level 40, st at level 39, st' at level 39).

Inductive ceval_count : com -> state -> state -> nat -> Prop :=
  | E'Skip : forall st,
      SKIP / st \\ st # 0
  | E'Ass  : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st \\ (t_update st l n) # 0
  | E'Seq : forall c1 c2 st st' st'' n1 n2,
      c1 / st  \\ st'  # n1 ->
      c2 / st' \\ st'' # n2 ->
      (c1 ;; c2) / st \\ st'' # (n1 + n2)
  | E'IfTrue : forall st st' b1 c1 c2 n,
      beval st b1 = true ->
      c1 / st \\ st' # n ->
      (TEST b1 THEN c1 ELSE c2 FI) / st \\ st' # n
  | E'IfFalse : forall st st' b1 c1 c2 n,
      beval st b1 = false ->
      c2 / st \\ st' # n ->
      (TEST b1 THEN c1 ELSE c2 FI) / st \\ st' # n
  | E'WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st # 0
  | E'WhileTrue : forall st st' st'' b1 c1 n1 n2,
      beval st b1 = true ->
      c1 / st \\ st' # n1 ->
      (WHILE b1 DO c1 END) / st' \\ st'' # n2 ->
      (WHILE b1 DO c1 END) / st \\ st'' # S (n1 + n2)

  where "c1 '/' st '\\' st' # n" := (ceval_count c1 st st' n).

Hint Constructors ceval_count.

Theorem ceval_count_complete: forall c st st',
  st =[ c ]=> st' -> exists n, c / st \\ st' # n.
Proof. intros c st st' Heval.
  induction Heval;
    try inversion IHHeval1;
    try inversion IHHeval2;
    try inversion IHHeval;
    eauto. Qed.

Theorem ceval_count_sound: forall c st st' n,
  c / st \\ st' # n -> st =[ c ]=> st'.
Proof. intros c st st' n Heval. induction Heval; eauto. Qed.

Theorem pe_compare_nil_lookup: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall V, pe_lookup pe_st1 V = pe_lookup pe_st2 V.
Proof. intros pe_st1 pe_st2 H V.
  apply (pe_compare_correct pe_st1 pe_st2 V).
  rewrite H. intro. inversion H0. Qed.

Theorem pe_compare_nil_update: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall st, pe_update st pe_st1 = pe_update st pe_st2.
Proof. intros pe_st1 pe_st2 H st.
  apply functional_extensionality. intros V.
  rewrite !pe_update_correct.
  apply pe_compare_nil_lookup with (V:=V) in H.
  rewrite H. reflexivity. Qed.

Reserved Notation "c' '/' pe_st' '/' c'' '/' st '\\' st'' '#' n"
  (at level 40, pe_st' at level 39, c'' at level 39,
   st at level 39, st'' at level 39).

Inductive pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)
                         (st:state) (st'':state) (n:nat) : Prop :=
  | pe_ceval_count_intro : forall st' n',
    st =[ c' ]=> st' ->
    c'' / pe_update st' pe_st' \\ st'' # n' ->
    n' <= n ->
    c' / pe_st' / c'' / st \\ st'' # n
  where "c' '/' pe_st' '/' c'' '/' st '\\' st'' '#' n" :=
        (pe_ceval_count c' pe_st' c'' st st'' n).

Hint Constructors pe_ceval_count.

Lemma pe_ceval_count_le: forall c' pe_st' c'' st st'' n n',
  n' <= n ->
  c' / pe_st' / c'' / st \\ st'' # n' ->
  c' / pe_st' / c'' / st \\ st'' # n.
Proof. intros c' pe_st' c'' st st'' n n' Hle H. inversion H.
  econstructor; try eassumption. omega. Qed.

Theorem pe_com_complete:
  forall c pe_st pe_st' c' c'', c / pe_st \\ c' / pe_st' / c'' ->
  forall st st'' n,
  (c / pe_update st pe_st \\ st'' # n) ->
  (c' / pe_st' / c'' / st \\ st'' # n).
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe; intros st st'' n Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - (* PE_AssStatic *) econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. apply E'Skip. auto.
  - (* PE_AssDynamic *) econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    apply E'Skip. auto.
  - (* PE_Seq *)
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. omega.
  - (* PE_If *) inversion Heval; subst.
    + (* E'IfTrue *) edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption. eassumption.
    + (* E_IfFalse *) edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption. eassumption.
  - (* PE_WhileTrue *)
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. omega.
  - (* PE_While *) inversion Heval; subst.
    + (* E_WhileFalse *) econstructor. apply E_IfFalse.
      rewrite <- pe_bexp_correct. assumption.
      apply eval_assign.
      rewrite <- assign_removes. inversion H2; subst; auto.
      auto.
    + (* E_WhileTrue *)
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      econstructor. apply E_IfTrue.
      rewrite <- pe_bexp_correct. assumption.
      repeat eapply E_Seq; eauto. apply eval_assign.
      rewrite -> pe_compare_update, <- assign_removes. eassumption.
      omega.
  - (* PE_WhileFixedLoop *) exfalso.
    generalize dependent (S (n1 + n2)). intros n.
    clear - H H0 IHHpe1 IHHpe2. generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + (* E'WhileFalse *) rewrite pe_bexp_correct, H in H7. inversion H7.
    + (* E'WhileTrue *)
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H0) in H7.
      apply H1 in H7; [| omega]. inversion H7.
  - (* PE_WhileFixed *) generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + (* E'WhileFalse *) rewrite pe_bexp_correct in H8. eauto.
    + (* E'WhileTrue *) rewrite pe_bexp_correct in H5.
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H1) in H8.
      apply H2 in H8; [| omega]. inversion H8.
      econstructor; [ eapply E_WhileTrue; eauto | eassumption | omega].
Qed.

Theorem pe_com_sound:
  forall c pe_st pe_st' c' c'', c / pe_st \\ c' / pe_st' / c'' ->
  forall st st'' n,
  (c' / pe_st' / c'' / st \\ st'' # n) ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe;
    intros st st'' n [st' n' Heval Heval' Hle];
    try (inversion Heval; []; subst);
    try (inversion Heval'; []; subst); eauto.
  - (* PE_AssStatic *) rewrite <- pe_update_update_add. apply E_Ass.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - (* PE_AssDynamic *) rewrite <- pe_update_update_remove. apply E_Ass.
    rewrite <- pe_aexp_correct. reflexivity.
  - (* PE_Seq *) eapply E_Seq; eauto.
  - (* PE_IfTrue *) apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - (* PE_IfFalse *) apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - (* PE_If *) inversion Heval; subst; inversion H7; subst; clear H7.
    + (* E_IfTrue *)
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
    + (* E_IfFalse *)
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe2. eauto.
  - (* PE_WhileFalse *) apply E_WhileFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
  - (* PE_WhileTrue *) eapply E_WhileTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe1. eauto. eapply IHHpe2. eauto.
  - (* PE_While *) inversion Heval; subst.
    + (* E_IfTrue *)
      inversion H9. subst. clear H9.
      inversion H10. subst. clear H10.
      eapply ceval_deterministic in H11; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      eapply E_WhileTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
      eapply IHHpe2. eauto.
    + (* E_IfFalse *) apply ceval_count_sound in Heval'.
      eapply ceval_deterministic in H9; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      inversion H2; subst.
      * (* c2'' = SKIP *) inversion Heval'. subst. apply E_WhileFalse.
        rewrite -> pe_bexp_correct. assumption.
      * (* c2'' = WHILE b1 DO c1 END *) assumption.
  - (* PE_WhileFixedEnd *) eapply ceval_count_sound. apply Heval'.
  - (* PE_WhileFixedLoop *)
    apply loop_never_stops in Heval. inversion Heval.
  - (* PE_WhileFixed *)
    clear - H1 IHHpe1 IHHpe2 Heval.
    remember (WHILE pe_bexp pe_st b1 DO c1';; c2' END)%imp as c'.
    induction Heval;
      inversion Heqc'; subst; clear Heqc'.
    + (* E_WhileFalse *) apply E_WhileFalse.
      rewrite pe_bexp_correct. assumption.
    + (* E_WhileTrue *)
      assert (IHHeval2' := IHHeval2 (refl_equal _)).
      apply ceval_count_complete in IHHeval2'. inversion IHHeval2'.
      clear IHHeval1 IHHeval2 IHHeval2'.
      inversion Heval1. subst.
      eapply E_WhileTrue. rewrite pe_bexp_correct. assumption. eauto.
      eapply IHHpe2. econstructor. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H1). eassumption. apply le_n.
Qed.

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' / SKIP ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (exists st', st =[ c' ]=> st' /\ pe_update st' pe_st' = st'').
Proof. intros c pe_st pe_st' c' H st st''. split.
  - (* -> *) intros Heval.
    apply ceval_count_complete in Heval. inversion Heval as [n Heval'].
    apply pe_com_complete with (st:=st) (st'':=st'') (n:=n) in H.
    inversion H as [? ? ? Hskip ?]. inversion Hskip. subst. eauto.
    assumption.
  - (* <- *) intros [st' [Heval Heq]]. subst st''.
    eapply pe_com_sound in H. apply H.
    econstructor. apply Heval. apply E'Skip. apply le_n.
Qed.

End Loop.

(* ################################################################# *)
(** * 流程图程序的部分求值 *)

(** 除了直接对 [WHILE] 的循环直接进行部分求值，一种对命令式程序进行部分求值
    的标准方式是将他们转换为_'流程图（Flowcharts）'_。换句话说，为我们的语言
    添加标签和跳转会使部分求值更容易。流程图程序的部分求值结果是一个剩余流程图。
    幸运的话，剩余流程图程序中的跳转会被转换回 [WHILE] 循环，但一般来说这可
    能不会发生；在这里我们并不追求达成这一点。*)

(* ================================================================= *)
(** ** 基本块 *)

(** 一个流程图程序由_'基本块（basic blocks）'_构成，我们用归纳类型 [block]
    来表示它。一个基本块是一个赋值语句（[Assign] 构造子）序列，并以条件跳转（[If]
    构造子）或者无条件跳转（[Goto] 构造子）结束。跳转的目标由_'标签（labels）'_所指明，
    其可为任意类型。因此，我们用标签的类型来参数化 [block] 类型。*)

Inductive block (Label:Type) : Type :=
  | Goto : Label -> block Label
  | If : bexp -> Label -> Label -> block Label
  | Assign : string -> aexp -> block Label -> block Label.

Arguments Goto {Label} _.
Arguments If   {Label} _ _ _.
Arguments Assign {Label} _ _ _.

(** 我们用上面 Imp 的“奇或偶”程序作为例子。将这个程序转换为流程图程序需要 4
    个标签，因此我们定义如下类型。*)

Inductive parity_label : Type :=
  | entry : parity_label
  | loop  : parity_label
  | body  : parity_label
  | done  : parity_label.

(** 下面的 [block] 是一个基本块，构成了例子程序的 [body] 标签所代表的基本块。*)

Definition parity_body : block parity_label :=
  Assign Y (Y - 1)
   (Assign X (1 - X)
     (Goto loop)).

(** 给定一个初始状态，对基本块的求值是计算出最终状态和跳转的目标标签。
    由于基本块不包含循环或其他控制结构，对基本块的求值是一个全函数——我们不需要
    担心非停机性。*)

Fixpoint keval {L:Type} (st:state) (k : block L) : state * L :=
  match k with
  | Goto l => (st, l)
  | If b l1 l2 => (st, if beval st b then l1 else l2)
  | Assign i a k => keval (t_update st i (aeval st a)) k
  end.

Example keval_example:
  keval empty_st parity_body
  = ((X !-> 1 ; Y !-> 0), loop).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 流程图程序 *)

(** 一个流程图程序是一个查找函数将标签映射到基本块。事实上，有的标签是
    _'停机状态（halting state）'_并且不被映射到任何基本块。因此准确地说，一个
    流程图程序 [program] 是一个将 [L] 映射到到 [option (block L)]
    的函数，其中 [L] 是标签的类型。 *)

Definition program (L:Type) : Type := L -> option (block L).

Definition parity : program parity_label := fun l =>
  match l with
  | entry => Some (Assign X 0 (Goto loop))
  | loop => Some (If (1 <= Y) body done)
  | body => Some parity_body
  | done => None (* halt *)
  end.

(** 不同与基本块，一个程序可能不会终止，因此我们把程序的求值建模为归纳关系 [peval]
    而非递归函数。*)

Inductive peval {L:Type} (p : program L)
  : state -> L -> state -> L -> Prop :=
  | E_None: forall st l,
    p l = None ->
    peval p st l st l
  | E_Some: forall st l k st' l' st'' l'',
    p l = Some k ->
    keval st k = (st', l') ->
    peval p st' l' st'' l'' ->
    peval p st l st'' l''.

Example parity_eval: peval parity empty_st entry  empty_st done.
Proof. erewrite f_equal with (f := fun st => peval _ _ _ st _).
  eapply E_Some. reflexivity. reflexivity.
  eapply E_Some. reflexivity. reflexivity.
  apply E_None. reflexivity.
  apply functional_extensionality. intros i. rewrite t_update_same; auto.
Qed.

(* ================================================================= *)
(** ** 基本块和流程图程序的部分求值 *)

(** 部分求值系统地改变了标签类型：如果标签类型是 [L]，那么它会变为 [pe_state * L]。
    因此源程序中的同同一个标签可能会未折叠、或展开多次，成为多个标签并和不同的部分状态配
    对在一起。比如说，[parity] 程序中的 [loop] 标签会变为两个标签：[([(X,0)], loop)]
    和 [([(X,1)], loop)]。标签类型的改变也在下面定义的 [pe_block] 和 [pe_program]
    的类型中反映出来。*)

Fixpoint pe_block {L:Type} (pe_st:pe_state) (k : block L)
  : block (pe_state * L) :=
  match k with
  | Goto l => Goto (pe_st, l)
  | If b l1 l2 =>
    match pe_bexp pe_st b with
    | BTrue  => Goto (pe_st, l1)
    | BFalse => Goto (pe_st, l2)
    | b'     => If b' (pe_st, l1) (pe_st, l2)
    end
  | Assign i a k =>
    match pe_aexp pe_st a with
    | ANum n => pe_block (pe_add pe_st i n) k
    | a' => Assign i a' (pe_block (pe_remove pe_st i) k)
    end
  end.

Example pe_block_example:
  pe_block [(X,0)] parity_body
  = Assign Y (Y - 1) (Goto ([(X,1)], loop)).
Proof. reflexivity. Qed.

Theorem pe_block_correct: forall (L:Type) st pe_st k st' pe_st' (l':L),
  keval st (pe_block pe_st k) = (st', (pe_st', l')) ->
  keval (pe_update st pe_st) k = (pe_update st' pe_st', l').
Proof. intros. generalize dependent pe_st. generalize dependent st.
  induction k as [l | b l1 l2 | i a k];
    intros st pe_st H.
  - (* Goto *) inversion H; reflexivity.
  - (* If *)
    replace (keval st (pe_block pe_st (If b l1 l2)))
       with (keval st (If (pe_bexp pe_st b) (pe_st, l1) (pe_st, l2)))
       in H by (simpl; destruct (pe_bexp pe_st b); reflexivity).
    simpl in *. rewrite pe_bexp_correct.
    destruct (beval st (pe_bexp pe_st b)); inversion H; reflexivity.
  - (* Assign *)
    simpl in *. rewrite pe_aexp_correct.
    destruct (pe_aexp pe_st a); simpl;
      try solve [rewrite pe_update_update_add; apply IHk; apply H];
      solve [rewrite pe_update_update_remove; apply IHk; apply H].
Qed.

Definition pe_program {L:Type} (p : program L)
  : program (pe_state * L) :=
  fun pe_l => match pe_l with | (pe_st, l) =>
                option_map (pe_block pe_st) (p l)
              end.

Inductive pe_peval {L:Type} (p : program L)
  (st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : Prop :=
  | pe_peval_intro : forall st' pe_st',
    peval (pe_program p) st (pe_st, l) st' (pe_st', l') ->
    pe_update st' pe_st' = st'o ->
    pe_peval p st pe_st l st'o l'.

Theorem pe_program_correct:
  forall (L:Type) (p : program L) st pe_st l st'o l',
  peval p (pe_update st pe_st) l st'o l' <->
  pe_peval p st pe_st l st'o l'.
Proof. intros.
  split.
  - (* -> *) intros Heval.
    remember (pe_update st pe_st) as sto.
    generalize dependent pe_st. generalize dependent st.
    induction Heval as
      [ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ];
      intros st pe_st Heqsto; subst sto.
    + (* E_None *) eapply pe_peval_intro. apply E_None.
      simpl. rewrite Hlookup. reflexivity. reflexivity.
    + (* E_Some *)
      remember (keval st (pe_block pe_st k)) as x.
      destruct x as [st' [pe_st' l'_]].
      symmetry in Heqx. erewrite pe_block_correct in Hkeval by apply Heqx.
      inversion Hkeval. subst st'o l'_. clear Hkeval.
      edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.
      eapply pe_peval_intro; [| reflexivity]. eapply E_Some; eauto.
      simpl. rewrite Hlookup. reflexivity.
  - (* <- *) intros [st' pe_st' Heval Heqst'o].
    remember (pe_st, l) as pe_st_l.
    remember (pe_st', l') as pe_st'_l'.
    generalize dependent pe_st. generalize dependent l.
    induction Heval as
      [ st [pe_st_ l_] Hlookup
      | st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']
        Hlookup Hkeval Heval ];
      intros l pe_st Heqpe_st_l;
      inversion Heqpe_st_l; inversion Heqpe_st'_l'; repeat subst.
    + (* E_None *) apply E_None. simpl in Hlookup.
      destruct (p l'); [ solve [ inversion Hlookup ] | reflexivity ].
    + (* E_Some *)
      simpl in Hlookup. remember (p l) as k.
      destruct k as [k|]; inversion Hlookup; subst.
      eapply E_Some; eauto. apply pe_block_correct. apply Hkeval.
Qed.


(* Fri Jul 19 00:33:17 UTC 2019 *)
