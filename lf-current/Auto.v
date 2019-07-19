(** * Auto: 更多的自动化 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import omega.Omega.
From LF Require Import Maps.
From LF Require Import Imp.

(** 到目前为止，我们大多使用的都是 Coq 策略系统中手动的部分。
    在本章中，我们会学习更多 Coq 强大的自动化特性：通过 [auto]
    策略进行证明搜索，通过 [Ltac] 前提搜索器进行自动正向推理，以及通过
    [eapply] 和 [eauto] 推迟存在性变量的实例化。这些特性配合 Ltac
    的脚本功能可以极大地缩短证明！如果使用得当，它们还会提高证明的可维护性，
    在以后修改证明的底层定义时也会更加健壮。对 [auto] 和 [eauto]
    更加深入的探讨可参阅_'《编程语言基础》'_的 [UseAuto] 一章。

    还有另一大类自动化方式我们所言不多，即内建的对特定种类问题的决策算法：
    [omega] 就是这样的例子，不过还有其它的。这一主题我们会以后再谈。

    我们从以下证明开始，加上一些[Imp]中的小改动。
    我们将分几个阶段来简化此证明。 *)

(** 首先，我们定义一小段 Ltac 宏，将常用的模式压缩成单个指令。 *)
Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* 断言的证明 *) apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b 求值为 true *)
    apply IHE1. assumption.
  - (* b 求值为 false（矛盾） *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H5. inversion H5.
  - (* b 求值为 false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b 求值为 false *)
    reflexivity.
  - (* b 求值为 true（矛盾） *)
    rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1.
    { (* 断言的证明 *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * [auto] 策略 *)

(** 迄今为止，我们的证明脚本大多是按名称来应用相关的前提或引理的，一次一个。 *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

(** [auto] 策略可以_'搜索'_一系列能够证明待证目标的应用来免除这些苦役：*)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** 任何能够被以下策略的组合解决的待证目标，都能用 [auto] 来解决：
     - [intros]
     - [apply]（默认使用局部上下文中的前提）。 *)

(** 使用 [auto] 一定是“安全”的，它不会失败，也不会改变当前证明的状态：
    [auto] 要么完全解决它，要么什么也不做。 *)

(** 下面是个更有趣的例子，它展示了 [auto] 的强大： *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** 理论上来说，搜索可能需要任意长的时间，此时可通过参数来控制
    [auto] 默认的搜索深度。 *)

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* 当 [auto] 无法解决此目标时，它就什么也不做 *)
  auto.
  (* 可选的参数用来控制它的搜索深度（默认为 5） *)
  auto 6.
Qed.

(** 在搜索当前目标的潜在证明时， [auto] 会同时考虑当前上下文中的前提，
    以及一个包含其它引理或构造子的_'提示数据库'_。
    某些关于相等关系和逻辑运算符的事实默认已经安装到提示数据库中了。 *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(** 我们可以为某次 [auto] 的调用扩展提示数据库，只需使用“[auto using ...]”。 *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

(** 当然, 在证明过程中经常会用到一些特定的构造子和引理，
    我们可以将它们加入全局提示数据库中，方法是在顶层使用：

      Hint Resolve T.

    其中 [T] 是某个顶层的定理，或者是某个归纳定义的命题
    （即所有类型都是一个蕴含式）的构造子。我们也可以使用简写

      Hint Constructors c.

    来告诉 Coq 对归纳定义 [c] 的_'所有'_构造子都执行 [Hint Resolve]。

    有时我们还需要

      Hint Unfold d.

    其中 [d] 是个已定义的符号，这样 [auto] 就知道要展开使用 [d]，
    以此来获得更多使用已知的引理的机会。 *)

(** 我们也可以定义特殊化的提示数据库，让它只在需要时激活。详情见 Coq 参考手册。 *)

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* 从数据库中找出提示 *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Qed.

(** 我们来初次尝试简化 [ceval_deterministic] 的证明脚本。 *)

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
       induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b 求值为 false（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b 求值为 true（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b 求值为 true（矛盾） *)
      rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.

(** 如果在证明中我们会反复用到某个策略，呢么可以使用一个 [Proof]
    指令的变体将它作为证明中的默认策略。例如 [Proof with t]（其中 [t]
    为任意一个策略）能够让我们在证明中将 [t1...] 用作 [t1;t] 的简写。
    作为示范，下面是以上证明的另一个版本，它用到了 [Proof with auto]。 *)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *)
    + (* b 求值为 false（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b 求值为 true（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b 求值为 true（矛盾） *)
      rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

(* ################################################################# *)
(** * 搜索前提 *)

(** 证明变得更简单了，但还是有些烦人的重复。我们先从矛盾的情况着手。
    这些矛盾都是因为我们同时有

      H1: beval st b = false

    和

      H2: beval st b = true

    这两个前提。矛盾很显然，但证明却有点麻烦：我们必须找到 [H1] 和 [H2]
    这两个前提，用一次 [rewrite] 后再用一次 [inversion]。我们希望自动化此过程。

    （实际上，Coq 有个内建的 [congruence] 策略来处理这种情况。
    不过我们暂时先忽略它的存在，为的是示范如何自己构建正向推理的策略。）

    第一步，我们可以通过在 Ltac 中编写一个小函数来抽象出有问题的脚本。 *)

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b 求值为 false（矛盾） *)
      rwinv H H5.
  - (* E_IfFalse *)
    + (* b 求值为 true（矛盾） *)
      rwinv H H5.
  - (* E_WhileFalse *)
    + (* b 求值为 true（矛盾） *)
      rwinv H H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rwinv H H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. Qed.

(** 此例相比之前略有改进，但我们更希望 Coq 能替我们找到相关的假设。
    Ltac 中的 [match goal] 功能可达成此目的。 *)

Ltac find_rwinv :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwinv H1 H2
  end.

(** [match goal] 会查找两个不同的，形如等式的前提，
    其左式为两个相同的任意表达式 [E]，而右式为两个互相矛盾的布尔值。
    如果找到了这样的前提，就把 [H1] 和 [H2] 绑定为它们的名字，
    并将 [rwinv] 策略应用到 [H1] 和 [H2] 上。

    把此策略添加到每一个归纳证明的情况中，就能把所有的矛盾情况都解决了。 *)

Theorem ceval_deterministic''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_WhileTrue *)
    + (* b 求值为 true *)
      assert (st' = st'0) as EQ1 by auto.
      subst st'0.
      auto. Qed.

(** 现在我们来看看剩下的情况。每种情况都应用了带条件的前提以得到一个等式。
    目前我们把这些等式重述为断言，因此我们必须猜出需要的等式是什么
    （虽然可以用 [auto] 证明它们）。另一种方式是找出用到的有关前提，
    然后用它们进行 [rewrite] 改写，类似于这样： *)

Theorem ceval_deterministic'''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *. auto.
  - (* E_WhileTrue *)
    + (* b 求值为 true *)
      rewrite (IHE1_1 st'0 H3) in *. auto. Qed.

(** 现在用于改写的相关前提可以自动查找了。 *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

(** 模式 [forall x, ?P x -> ?L = ?R] 会匹配任何任何形如
    “对于所有的 [x]，_'[x] 的某些性质'_蕴含_'某些等式'_”的前提。
    [x] 的性质被绑定为模式变量 [P]，而该等式的左式和右式会分别绑定为
    [L] 和 [R]。此前提的名字会被绑定为 [H1]。之后模式 [?P ?X]
    会匹配任何提供了“[P] 对于某个具体的 [X] 成立的证据”的前提。
    如果两个模式均成功，我们会在所有的前提和目标中应用 [rewrite] 策略改写
    （即，用 [X] 来实例化量化的 [x] 并将 [H2] 作为 [P X] 所需的证据提供）。

    还剩一个问题：通常，可能有好几对前提都具有这种一般形式，
    而挑出我们真正需要的好像比较困难。不过关键在于我们要认识到其实可以
    _'全试一遍'_！以下是具体方法：

    - 每一个 [match goal] 在执行时都会不停地查找可行的一对前提，
      直到右式 RHS 匹配成功；如果没有这样的一对前提则会失败。
    - [rewrite] 在得到一个形如 [X = X] 的平凡等式时会失败。
    - 我们可以把整体策略包装在 [repeat] 中，这样就可以一直进行有用的改写，
      直到只剩下平凡的了。 *)

Theorem ceval_deterministic''''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv;
    repeat find_eqn; auto.
Qed.

(** 这种方法的巨大回报是，面对我们语言的适度变化时，我们的证明脚本会更加健壮。
    比如，我们可以为该语言增加一个 [REPEAT] 指令。 *)

Module Repeat.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

(** [REPEAT] 的行为和 [WHILE] 类似，只是循环条件会在每次循环体执行完
    _'之后'_ 执行，且只在循环条件为_'false'_时重复执行。
    因此，循环体至少会被执行一次。 *)

Notation "'SKIP'" :=
   CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'REPEAT' c 'UNTIL' b 'END'" :=
  (CRepeat c b) (at level 80, right associativity).

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ REPEAT c UNTIL b END ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ REPEAT c UNTIL b END ]=> st'' ->
      st  =[ REPEAT c UNTIL b END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** 我们对确定性证明的第一次尝试并不成功：[E_RepeatEnd] 和 [E_RepeatLoop]
    这两种情况并没有被之前的自动化处理。 *)

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b 求值为 false（矛盾） *)
       find_rwinv.
       (* 哎呀！为什么刚才 [find_rwinv] 没有为我们解决这个问题呢？
          因为我们把顺序搞错了。 *)
  - (* E_RepeatLoop *)
     + (* b 求值为 true（矛盾） *)
        find_rwinv.
Qed.

(** 幸运的是，我们只需交换 [find_eqn] 和 [find_rwinv]
    的调用顺序就能修复这一点。 *)

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inv E2; repeat find_eqn; try find_rwinv; auto.
Qed.

End Repeat.

(** 这些例子为了让大家看看 Coq 中的“超级自动化”可以做到什么。
    [match goal] 在使用时的的细节十分复杂，调试也很不方便。
    但至少在证明时值得加入它来简化证明，避免繁琐的工作，
    并为未来的修改做好准备。 *)

(* ================================================================= *)
(** ** 变体 [eapply] 和 [eauto] *)

(** 作为本章的结尾，我们来介绍一种更加方便的特性：
    它能够推迟量词的实例化。为了引出此特性，我们来回忆一下[Imp]
    中的这个例子： *)

Example ceval_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* 我们补充了中间状态 [st']... *)
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

(** 在证明的第一步，我们显式地提供了一个略长的表达式来帮助 Coq
    为 [E_Seq] 构造子实例化一个“隐藏”的参数。需要它的原因在于
    [E_Seq] 的定义...

          E_Seq : forall c1 c2 st st' st'',
            st  =[ c1 ]=> st'  ->
            st' =[ c2 ]=> st'' ->
            st  =[ c1 ;; c2 ]=> st''

   它是对 [st'] 的量化，而且并没有出现在结论中，因此将其结论与目标状态统一
   并不能帮助 Coq 为此变量找到合适的值。如果我们忽略 [with]，这一步就会失败
   （"Error: Unable to find an instance for the variable [st']"）。

   该错误的愚蠢指出在于适合 [st'] 的值其实在后面的步骤中会相当明显，
   就在我们应用 [E_Ass] 的地方。如果 Coq 能够等到这一步，就没必要显式地给出该值了。
   这正是 [eapply] 策略所能做到的： *)

Example ceval'_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  eapply E_Seq. (* 1 *)
  - apply E_Ass. (* 2 *)
    reflexivity. (* 3 *)
  - (* 4 *) apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

(** [eapply H] 的行为和 [apply H] 一样，只是在它统一完目标状态和
    [H] 的结论之后，它并不会在引入所有变量的过程中，
    麻烦你去检查它们在统一时是否被赋予了具体的值。

    如果你循着上面的证明步骤，就会看到 [1] 处的目标状态在生成的两个子目标中，
    都提到了_'存在性变量'_ [?st']。下一步，即把我们待带到 [2] 处的一步，
    会把 [?st'] 替换成一个具体的值。这个新值包含一个新的存在性变量 [?n]，
    它会被后面 [3] 处的 [reflexivity] 步骤依次实例化。当我们开始着手第二个子目标时
    （[4] 处），我们观察到此子目标中出现的 [?st'] 已经被替换成了在第一个子目标中给出的值。 *)

(** 我们目前学过的几个策略，包括 [exists]、[constructor] 和 [auto] 都有类似的变体。
    例如，下面是一个使用了 [eauto] 的证明： *)

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := (Y !-> 2 ; X !-> 1).
Definition st21 := (Y !-> 1 ; X !-> 2).

Example eauto_example : exists s',
  st21 =[
    TEST X <= Y
      THEN Z ::= Y - X
      ELSE Y ::= X + Z
    FI
  ]=> s'.
Proof. eauto. Qed.

(** [eauto] 的策略和 [auto] 一样，除了它会使用 [eapply] 而非 [apply]。

    专业提示：有人可能会想，既然 [eapply] 和 [eauto] 比 [apply] 和 [auto]
    更强大，那么总是用它们不就好了。不幸的是，它们明显更慢，特别是 [eauto]。
    Coq 专家倾向于主要使用 [apply] 和 [auto]，只在普通的版本无法做这些工作时才使用
    [e] 开头的变体。 *)


(* Fri Jul 19 00:32:21 UTC 2019 *)
