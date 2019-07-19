(** * Equiv: 程序的等价关系 *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From PLF Require Import Imp.

(** *** 一些关于习题的建议：

    - 这里要进行的大多数 Coq 证明都与我们之前提供的类似。在做作业之前，
      请先花点时间，非形式化地在纸上以及在 Coq 中思考我们的证明，
      确保你完全理解了其中的每个细节。这会节省你大量的时间。

    - 我们现在进行的 Coq 证明已经足够复杂，几乎不可能再单靠“感觉”
      或乱撞的方式来完成证明了。你需要以“为何某个属性为真”以及“如何进行证明”
      的想法开始。完成此任务的最佳方式是在开始形式化证明前，至少先在纸上写出
      非形式化证明的梗概，即以直观的方式说服自己相信该定理成立，
      然后再进行形式化证明。或者，你也可以拉一个好友，尝试说服他此定理成立，
      然后形式化你的解释。

    - 请使用自动化工具来减少工作量！如果你全部显式地写出证明中的所有情况，
      那么本章中的证明会非常长。  *)

(* ################################################################# *)
(** * 行为的等价关系 *)

(** 在前面的章节中，我们探讨了一个非常简单的程序变换，即 [optimize_0plus]
    函数的正确性。我们考虑的编程语言为算术表达式语言的第一版，它没有变量，
    因此在该环境下，程序变换正确的意义非常容易定义：它产生的程序的求值结果
    应当总是与原始程序产生的数字相等。

    为了讨论整个 Imp 语言中程序变换，特别是赋值的正确性，
    我们需要考虑变量和状态的作用。 *)

(* ================================================================= *)
(** ** 定义 *)

(** 对于包含变量的 [aexp] 和 [bexp] 而言，我们所需的定义简单明了。
    只要在所有状态下，两个 [aexp] 或 [bexp] 的求值结果相同，
    我们就说他们的_'行为等价（behaviorally equivalent）'_。 *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** 下面是一些算术和布尔表达式等价的简单例子。 *)

Theorem aequiv_example: aequiv (X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0)%imp true.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** 对指令而言，情况则有些微妙。我们无法简单地说“如果在相同的初始状态下，
    两个指令求值的停机状态相同，那么这两个指令等价”，
    因为有些指令在某些初始状态下运行时根本不会在任何状态下停机！
    我们实际上需要的是：“若两个指令在任何给定的初始状态下，要么发散，
    要么在相同的状态下停机，则二者行为等价。”简单来说，就是：
    “若其中一个指令在某状态下停机，那么另一个也在该状态下停机，反之亦然。” *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** 简单示例 *)

(** 下面是一些指令等价的例子，我们首先从包含 [SKIP] 的简单程序变换开始： *)

Theorem skip_left : forall c,
  cequiv
    (SKIP;; c)
    c.
Proof.
  (* 课上已完成 *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** 练习：2 星, standard (skip_right)  

    请证明在某条指令之后添加 [SKIP] 后，两程序会等价 *)

Theorem skip_right : forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 同样，下面是一个优化 [TEST] 的简单程序变换： *)

Theorem TEST_true_simple : forall c1 c2,
  cequiv
    (TEST true THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. inversion H5.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.

(** 当然，人类程序员是不会写把断言（guard）直接写成 [true] 的条件分支的。
    不过当断言_'等价于真'_的情况时就会写出来： 

    _'定理'_：若 [b] 等价于 [BTrue]，则 [TEST b THEN c1 ELSE c2 FI] 等价于 [c1]。 
   _'证明'_：

     - ([->]) 我们必须证明，对于所有的 [st] 和 [st']，若 [st =[
       TEST b THEN c1 ELSE c2 FI ]=> st'] 则 [st =[ c1 ]=> st']。

       能够应用于 [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'] 的证明规则只有两条：
       [E_IfTrue] 和 [E_IfFalse]。

       - 假设 [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'] 证明自 [E_IfTrue]
         这条证明规则。若使用证明规则 [E_IfTrue] 其必备的前提条件 [st =[ c1 ]=> st']
         必为真，而这正好是我们的证明所需要的条件。

       - 另一方面, 假设 [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'] 证明自
         [E_IfFalse]。我们能得知 [beval st b = false] 和 [st =[ c2 ]=> st']。

         之前提到 [b] 等价于 [BTrue], 即对于所有 [st]，有 [beval st b = beval st
         BTrue]。具体来说就是 [beval st b = true] 成立，因而 [beval st BTrue =
         true] 成立。然而，之前假设 [E_IfFalse] 必备的前提条件 [beval st b = false]
         也成立，这就构成了一组矛盾，因此不可能使用了 [E_IfFalse] 这条证明规则。

     - ([<-]) 我们必须证明，对于所有 [st] 和 [st']，若[st =[ c1 ]=> st']
       则 [IFB b THEN c1 ELSE c2 FI / st \\ st']。

       已知 [b] 等价于 [BTrue]，我们知道 [beval st b] = [beval st BTrue] = [true]。
       结合 [st =[ c1 ]=> st'] 这条假设，我们能应用 [E_IfTrue] 来证明
       [st =[ TEST b THEN c1 ELSE c2 FI ]=> st']。 []

   下面是这个证明的形式化版本： *)

Theorem TEST_true: forall b c1 c2,
  bequiv b BTrue  ->
  cequiv
    (TEST b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b 求值为 true *)
      assumption.
    + (* b 求值为 false（矛盾） *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

(** **** 练习：2 星, standard, recommended (TEST_false)  *)
Theorem TEST_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (TEST b THEN c1 ELSE c2 FI)
    c2.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (swap_if_branches)  

    证明我们可以通过对断言取反来交换 IF 的两个分支 *)

Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (TEST b THEN e1 ELSE e2 FI)
    (TEST BNot b THEN e2 ELSE e1 FI).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 对于 [WHILE] 循环，我们能够给出一组相似的定理：当循环的断言等价于 [BFalse]
    时它等价于 [SKIP]；当循环的断言等价于 [BTrue] 时它等价于 [WHILE BTrue DO
    SKIP END]（或任意不停机的程序）。前者比较简单。 *)

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileFalse.
    rewrite Hb.
    reflexivity.  Qed.

(** **** 练习：2 星, advanced, optional (WHILE_false_informal)  

    写出 [WHILE_false] 的非形式化证明。

(* 请在此处解答 *)

    [] *)

(** 为了证明第二个定理，我们需要一个辅助引理：[WHILE] 循环在其断言等价于 [BTrue]
    时不会停机。 *)

(** _'引理'_：若 [b] 等价于 [BTrue]，则无法出现
    [st =[ WHILE b DO c END ]=> st'] 的情况。

    _'证明'_：假设 [st =[ WHILE b DO c END ]=> st']。我们将证明通过对
    [st =[ WHILE b DO c END ]=> st'] 使用归纳法会导出矛盾。需要考虑只有
    [E_WhileFalse] 和 [E_WhileTrue] 两种情况，其它情况则矛盾。

      - 假设 [st =[ WHILE b DO c END ]=> st'] 使用规则 [E_WhileFalse] 证明。
        那么根据假设得出 [beval st b = false]。但它与 [b] 等价于 [BTrue] 矛盾。

      - 假设 [st =[ WHILE b DO c END ]=> st'] 使用规则 [E_WhileTrue]证明。
        我们必有：

      1. [beval st b = true]，
      2. 存在某个 [st0] 使得 [st =[ c ]=> st0] 且
         [st0 =[ WHILE b DO c END ]=> st']，
      3. 以及我们给出了导致矛盾的归纳假设 [st0 =[ WHILE b DO c END ]=> st']，

      我们根据 2 和 3 会得到矛盾。 [] *)

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( st =[ WHILE b DO c END ]=> st' ).
Proof.
  (* 课上已完成 *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END)%imp as cw eqn:Heqcw.
  induction H;
  (* 大多数证明规则无法应用，我们可通过反演（inversion）来去除它们： *)
  inversion Heqcw; subst; clear Heqcw.
  (* 我们只关心这两个关于 WHILE 循环的证明规则： *)
  - (* E_WhileFalse *) (* 矛盾 -- b 总为真！ *)
    unfold bequiv in Hb.
    (* [rewrite] 能实例化 [st] 中的量词 *)
    rewrite Hb in H. inversion H.
  - (* E_WhileTrue *) (* 直接使用 IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** 练习：2 星, standard, optional (WHILE_true_nonterm_informal)  

    试解释 [WHILE_true_nonterm] 的含义。

(* 请在此处解答 *)

    [] *)

(** **** 练习：2 星, standard, recommended (WHILE_true)  

    请证明以下定理。_'提示'_：你可能需要使用 [WHILE_true_nonterm] 。 *)

Theorem WHILE_true : forall b c,
  bequiv b true  ->
  cequiv
    (WHILE b DO c END)
    (WHILE true DO SKIP END).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 关于 [WHILE] 指令的更有趣的事实是，任何数量的循环体的副本在不改变意义
    的情况下均可被“展开”。循环展开在实际的编译器中是种常见的变换。 *)

Theorem loop_unrolling : forall b c,
  cequiv
    (WHILE b DO c END)
    (TEST b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* 课上已完成 *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* 不执行循环 *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* 执行循环 *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* 执行循环 *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + (* 不执行循环 *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

(** **** 练习：2 星, standard, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 证明涉及赋值的程序的属性经常会用到这一事实，即程序状态会根据其外延性
    （如 [x !-> m x ; m] 和 [m] 是相等的映射）来对待。 *)

Theorem identity_assignment : forall x,
  cequiv
    (x ::= x)
    SKIP.
Proof.
  intros.
  split; intro H; inversion H; subst.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x ::= x ]=> (x !-> st' x ; st')).
    { apply E_Ass. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** 练习：2 星, standard, recommended (assign_aequiv)  *)
Theorem assign_aequiv : forall (x : string) e,
  aequiv x e ->
  cequiv SKIP (x ::= e).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (equiv_classes)  *)

(** 给定下列程序，请按照它们在 [Imp] 中是否等价将这些程序分组。
    你的答案应该是一个列表的列表，其中每个子列表都表示一组等价的程序。
    例如，如果你认为程序 (a) 至 (h) 都互相等价，但不等价于 (i)，那么答案应当如下：

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    请在 [equiv_classes] 的定义下方写出你的答案。 *)

Definition prog_a : com :=
  (WHILE ~(X <= 0) DO
    X ::= X + 1
  END)%imp.

Definition prog_b : com :=
  (TEST X = 0 THEN
    X ::= X + 1;;
    Y ::= 1
  ELSE
    Y ::= 0
  FI;;
  X ::= X - Y;;
  Y ::= 0)%imp.

Definition prog_c : com :=
  SKIP%imp.

Definition prog_d : com :=
  (WHILE ~(X = 0) DO
    X ::= (X * Y) + 1
  END)%imp.

Definition prog_e : com :=
  (Y ::= 0)%imp.

Definition prog_f : com :=
  (Y ::= X + 1;;
  WHILE ~(X = Y) DO
    Y ::= X + 1
  END)%imp.

Definition prog_g : com :=
  (WHILE true DO
    SKIP
  END)%imp.

Definition prog_h : com :=
  (WHILE ~(X = X) DO
    X ::= X + 1
  END)%imp.

Definition prog_i : com :=
  (WHILE ~(X = Y) DO
    X ::= Y + 1
  END)%imp.

Definition equiv_classes : list (list com)
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * 行为等价的性质 *)

(** 接下来我们考虑程序等价的一些基本性质。 *)

(* ================================================================= *)
(** ** 行为等价是一种等价关系 *)

(** 首先, 我们验证 [aexps]、[bexps] 和 [com] 的确满足_'等价关系（equivalences）'_
    -- 也就是说，它同时满足自反性（reflexive）、对称性（symmetric）和传递性
      （transitive）。这些证明都很容易。*)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (st =[ c1 ]=> st' <-> st =[ c2 ]=> st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (st =[ c2 ]=> st'). apply H12. apply H23.  Qed.

(* ================================================================= *)
(** ** 行为等价是一种一致性 *)

(** 虽然不太明显，但行为等价也满足_'一致性（congruence）'_。
    即，如果两个子程序等价，那么当二者所在的更大的程序中只有二者不同时，
    这两个更大的程序也等价：

              aequiv a1 a1'
      -----------------------------
      cequiv (x ::= a1) (x ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;;c2) (c1';;c2')

    ...以及这些指令的更多其它形式。 *)

(** （注意这里使用的推理规则的记法并不是定义的成部分，只是将一些
    合法的蕴含式用易读的方式写下而已。接下来我们将证明这些蕴含式。） *)

(** 在接下来的章节（[fold_constants_com_sound] 的证明）中，我们会用
    具体例子来说明这种一致性多么重要。不过它最主要意义在于，当我们在用
    一小部分程序替换大程序中等价的部分并证明替换前后程序的等价关系时，
    _'无需'_进行与不变的部分相关的证明。也就是说，程序的改变所产生的证明的工作量
    与改变的大小而非整个程序的大小成比例。 *)

Theorem CAss_congruence : forall x a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss x a1) (CAss x a1').
Proof.
  intros x a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** 循环的一致性更有趣, 因为它需要使用归纳法。

    _'定理'_: 对于 [WHILE]，等价关系是一种一致性 -- 即，若 [b1] 等价于 [b1'] 且 [c1]
    等价于 [c1']，那么 [WHILE b1 DO c1 END] 等价于 [WHILE b1' DO c1' END]。

    _'证明'_: 假设 [b1] 等价于 [b1'] 且 [c1] 等价于 [c1']。我们必须证明，
    对于每个 [st] 和 [st']，[st =[ WHILE b1 DO c1 END ]=> st'] 当且仅当
    [st =[ WHILE b1' DO c1' END ]=> st']。我们把两个方向分开考虑。

      - ([->]) 我们通过对 [st =[ WHILE b1 DO c1 END ]=> st'] 使用归纳法证明
        [st =[ WHILE b1 DO c1 END ]=> st'] 蕴含 [st =[ WHILE b1' DO c1' END ]=> st']。
        只有推导的最后所使用的规则为 [E_WhileFalse] 或 [E_WhileTrue]
        时才需要进行特别讨论。

          - [E_WhileFalse]：此时我们拥有假设的必备条件 [beval st b1 = false]
            和 [st = st']。但是，由于 [b1] 和 [b1'] 等价，我们有
            [beval st b1' = false]，然后应用 [E-WhileFalse] 得出我们需要的
            [st =[ WHILE b1' DO c1' END ]=> st']。

          - [E_WhileTrue]：此时我们拥有假设的必备条件 [beval st b1 = true]，以及
            对于某些状态 [st'0] 的 [st =[ c1 ]=> st'0] 和 [st'0 =[ WHILE b1 DO c1
            END ]=> st']，还有归纳假设 [st'0 =[ WHILE b1' DO c1' END ]=> st']。

            由于 [c1] 和 [c1'] 等价，我们有 [st =[ c1' ]=> st'0]；
            由于 [b1] 和 [b1'] 等价，我们有 [beval st b1' = true]。现在应用
            [E-WhileTrue]，得出我们所需的 [st =[ WHILE b1' DO c1' END ]=> st']。

      - ([<-]) 反之亦然。 [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* 课上已完成 *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END)%imp as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* 执行展示循环 *) rewrite <- Hb1e. apply H.
      * (* 执行主体 *)
        apply (Hc1e st st').  apply Hce1.
      * (* 执行之后的循环 *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END)%imp as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite -> Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* 执行展示循环 *) rewrite -> Hb1e. apply H.
      * (* 执行主体 *)
        apply (Hc1e st st').  apply Hce1.
      * (* 执行之后的循环 *)
        apply IHHce2. reflexivity.  Qed.

(** **** 练习：3 星, standard, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (TEST b THEN c1 ELSE c2 FI)
         (TEST b' THEN c1' ELSE c2' FI).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 例如，下面是两个等价的程序和它们等价关系的证明... *)

Example congruence_example:
  cequiv
    (* 程序 1： *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= 0
     ELSE
       Y ::= 42
     FI)
    (* 程序 1： *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= X - X   (* <--- 这里不同 *)
     ELSE
       Y ::= 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl.
      * symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

(** **** 练习：3 星, advanced, optional (not_congr)  

    我们已经证明了 [cequiv] 关系对指令同时满足等价关系和一致性。
    你能想出一个对于指令满足等价关系但_'不满足'_一致性的关系吗？ *)

(* 请在此处解答 

    [] *)

(* ################################################################# *)
(** * 程序变换 *)

(** _'程序变换（program transformation）'_是一种以某个程序作为输入，
    产生该程序的某种变体作为输出的函数。编译器优化中的常量折叠就是个经典的例子，
    然而程序变换并不仅限如此。 *)

(** 如果一个程序变换保留了其原始行为，那么它就是_'可靠（sound）'_的。 *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** 常量折叠变换 *)

(** 不引用变量的表达式为_'常量（constant）'_。

    常量折叠是一种找到常量表达式并把它们替换为其值的优化方法。 *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | APlus a1 a2  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp ((1 + 2) * X)
  = (3 * X)%imp.
Proof. reflexivity. Qed.

(** 注意此版本的常量折叠不包括优化平凡的加法等 -- 为简单起见，
    我们把注意力集中到单个优化上来。将其它简化表达式的方法加进来也不难，
    只是定义和证明会更长。 *)

Example fold_aexp_ex2 :
  fold_constants_aexp (X - ((0 * 6) + Y))%imp = (X - (0 + Y))%imp.
Proof. reflexivity. Qed.

(** 我们不仅可以将 [fold_constants_aexp] 优化成 [bexp]（如在 [BEq] 和 [BLe]
    的情况下），还可以查找常量_'布尔'_表达式并原地求值。 *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ~(false && true))%imp
  = true.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1))))%imp
  = ((X = Y) && true)%imp.
Proof. reflexivity. Qed.

(** 为了折叠指令中的常量，我们需要对所有内嵌的表达式应用适当的折叠函数。 *)

Open Scope imp.
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | x ::= a   =>
      x ::= (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | TEST b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue  => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => TEST b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
Close Scope imp.

Example fold_com_ex1 :
  fold_constants_com
    (* 原程序： *)
    (X ::= 4 + 5;;
     Y ::= X - 3;;
     TEST (X - Y) = (2 + 4) THEN SKIP
     ELSE Y ::= 0 FI;;
     TEST 0 <= (4 - (2 + 1)) THEN Y ::= 0
     ELSE SKIP FI;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp
  = (* 常量折叠后： *)
    (X ::= 9;;
     Y ::= X - 3;;
     TEST (X - Y) = 6 THEN SKIP
     ELSE Y ::= 0 FI;;
     Y ::= 0;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 常量折叠的可靠性 *)

(** 现在我们需要证明之前所做事情的正确性。 *)

(** 下面是对算术表达式的证明： *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum 和 AId 很显然 *)
    try reflexivity;
    (* 从 IH 和下面的观察出发很容易完成对 APlus、AMinus 和 AMult 情况的证明：
              aeval st (APlus a1 a2)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       （AMinus/minus 和 AMult/mult 同理） *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** 练习：3 星, standard, optional (fold_bexp_Eq_informal)  

    下面是布尔表达式常量折叠中 [BEq] 情况的可靠性的证明。
    请认真读完它再和之后的形式化证明作比较，然后补充完 [BLe] 情况的形式化证明
    （尽量不看之前 [BEq] 情况的证明）。

   _'定理'_：布尔值的常量折叠函数 [fold_constants_bexp] 是可靠的。

   _'证明'_：我们必须证明对于所有的布尔表达式 [b]，[b] 都等价于
   [fold_constants_bexp b]。我们对 [b] 使用归纳法。这里只给出了 [b]
   形如 [BEq a1 a2] 的情况。

   在本情况中，我们必须证明

       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).

   有两种情况需要考虑：

     - 首先，假设对于某些 [n1] 和 [n2] 而言有 [fold_constants_aexp a1 = ANum n1]
       和 [fold_constants_aexp a2 = ANum n2]。

       在此情况下，我们有

           fold_constants_bexp (BEq a1 a2)
         = if n1 =? n2 then BTrue else BFalse

       和

           beval st (BEq a1 a2)
         = (aeval st a1) =? (aeval st a2).

       根据算术表达式常量折叠的健全性（引理 [fold_constants_aexp_sound]）可得

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       和

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       因此

           beval st (BEq a1 a2)
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       此外，在分别考虑 [n1 = n2] 和 [n1 <> n2] 的情况后，容易看出

           beval st (if n1 =? n2 then BTrue else BFalse)
         = if n1 =? n2 then beval st BTrue else beval st BFalse
         = if n1 =? n2 then true else false
         = n1 =? n2.

       因此

           beval st (BEq a1 a2)
         = n1 =? n2.
         = beval st (if n1 =? n2 then BTrue else BFalse),

       正是所需的假设。

     - 另一方面，假设 [fold_constants_aexp a1] 和 [fold_constants_aexp a2]
       之一并非常量。此时，我们必须证明

           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),

       根据 [beval] 的定义，它等同于证明

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       但是，由于算术表达式的可靠性（定理 [fold_constants_aexp_sound]）可得出

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       本例证毕。  [] *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue 和 BFalse 是显然的 *)
    try reflexivity.
  - (* BEq *)
    simpl.

(** （当存在许多构造子时，使用归纳法会让给变量取名编程一件琐事，
    然而 Coq 并不总是能够选择足够好的变量名。我们可以使用 [rename] 重命名：
    策略 [rename a into a1] 会将当前目标和上下文中的 [a] 重命名为 [a1]。） *)

    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.

    (* 唯一有趣的是 a1 和 a2 在折叠后同时变为常量 *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    (* 请在此处解答 *) admit.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (fold_constants_com_sound)  

    完成以下证明的 [WHILE] 情况。 *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* TEST *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* （如果 if 没有被优化掉，那么我们很容易使用 IH 和
         [fold_constants_bexp_sound] 来得出证明。） *)
    + (* b 总为真 *)
      apply trans_cequiv with c1; try assumption.
      apply TEST_true; assumption.
    + (* b 总为假 *)
      apply trans_cequiv with c2; try assumption.
      apply TEST_false; assumption.
  - (* WHILE *)
    (* 请在此处解答 *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 再论 (0 + n) 优化的可靠性 *)

(** **** 练习：4 星, advanced, optional (optimize_0plus)  

    回顾_'逻辑基础'_ [Imp] 一章中 [optimize_0plus] 的定义：

    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.

   注意此函数是针对无状态的 [aexp] 编写的。

   请为 [aexp] [bexp] 和 [com] 都写一个带状态的新版本：

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   请证明这三个函数都具有可靠性，就像之前证明 [fold_constants_*] 那样。在
   [optimize_0plus_com] 的证明中你需要一致性引理 -- 否则证明过程会_'很长'_！

   接下来为指令定义一个优化器，它首先使用常量折叠（[fold_constants_com]）然后优化掉
   [0 + n] 项（使用 [optimize_0plus_com]）。

   - 请为此优化器写一个有意义的测试用例。

   - 证明此优化程序有可靠性。（这部分应该会_'很简单'_ 。）  *)

(* 请在此处解答 

    [] *)

(* ################################################################# *)
(** * 证明程序不等价 *)

(** 假设 [c1] 是形如 [X ::= a1;; Y ::= a2] 的指令，并且 [c2] 是形如
    [X ::= a1;; Y ::= a2'] 的指令，[a2'] 是把 [a2] 中所有 [X] 都替换为 [a1]
    后的结果。比如，[c1] 和 [c2] 可以像这样：

       c1  =  (X ::= 42 + 53;;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))

    很明显，在这个_'特定的例子中'_ [c1] 和 [c2] 是等价的。但是对一般程序而言，
    此结果是否成立？ *)

(** 我们马上就会发现这是不行的。不过且慢，现在，
    看你自己能否找出一个反例来。 *)

(** 以下形式化的定义描述了如何在算术表达式 [a] 中，
    将某个变量 [x] 的所有引用都替换成另一个表达式 [u] ： *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if eqb_string x x' then u else AId x'
  | APlus a1 a2  =>
      APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (42 + 53) (Y + X)%imp
  = (Y + (42 + 53))%imp.
Proof. reflexivity.  Qed.

(** 而这里是一个我们感兴趣的性质：它断言类似上述形式的 [c1] 和 [c2]
    总是等价的。  *)

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv (x1 ::= a1;; x2 ::= a2)
         (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

(** 遗憾的是, 这个性质_'并不'_总是成立 -- 即，它并不是对所有的
    [x1]、[x2]、[a1] 和 [a2] 都成立。

      cequiv (x1 ::= a1;; x2 ::= a2)
             (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

    我们使用反证法来证明这一点。假设对于所有的 [x1]、[x2]、[a1]
    和 [a2]，我们有

      cequiv (x1 ::= a1;; x2 ::= a2)
             (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

    考虑以下程序：

      X ::= X + 1;; Y ::= X

    注意

      empty_st =[ X ::= X + 1;; Y ::= X ]=> st1,

    其中 [st1 = (Y !-> 1 ; X !-> 1)].

    根据假设，我们知道

      cequiv (X ::= X + 1;;
              Y ::= X)
             (X ::= X + 1;;
              Y ::= X + 1)

    同时，根据 [cequiv] 的定义，我们有

      empty_st =[ X ::= X + 1;; Y ::= X + 1 ]=> st1.

    但是我们也能推导出

      empty_st =[ X ::= X + 1;; Y ::= X + 1 ]=> st2,

    其中 [st2 = (Y !-> 2 ; X !-> 1)]。但由于 [ceval] 是确定性的，而
    [st1 <> st2] ，这就造成了矛盾！  [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* 这里有个反例：假设 [subst_equiv_property]
     成立能够让我们证明以下两个程序等价... *)
  remember (X ::= X + 1;;
            Y ::= X)%imp
      as c1.
  remember (X ::= X + 1;;
            Y ::= X + 1)%imp
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ...我们来证明 [c2] 能够在两个不同的状态下停机：
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* 最后，因为程序求值的确定性而产生矛盾。 *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(** **** 练习：4 星, standard, optional (better_subst_equiv)  

    之前我们思考的等价关系也不全是妄言 -- 只要再增加一个条件，
    即变量 [X] 不在第一个赋值语句的右边出现，它就是正确的了。 *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (APlus a1 a2)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMinus a1 a2)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMult a1 a2).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  (* 请在此处解答 *) Admitted.

(** 使用 [var_not_used_in_aexp]，形式化并证明正确版本的 [subst_equiv_property]。 *)

(* 请在此处解答 

    [] *)

(** **** 练习：3 星, standard (inequiv_exercise)  

    证明无限循环不等价于 [SKIP] *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 扩展练习：非确定性 Imp *)

(** 正如之前所见（[Imp] 一章中的 [ceval_deterministic]），Imp
    的求值关系是确定性的。然而在一些实际的编程语言定义中，_'非确定性'_
    也是十分重要的一部分。例如，在很多指令式语言中（如 C 系的语言），
    函数参数的求值顺序是未指定的。程序片段

      x = 0;;
      f(++x, x)

    调用 [f] 时所用的参数可能是 [(1, 0)] 或者 [(1, 1)]，取决于编译器的选择。
    这可能会让程序员感到困惑，但给了编译器作者选择实现的自由。

    在此练习中，我们会用一个简单的非确定性指令来扩展 Imp，
    研究这种改变会对程序等价关系产生何种影响。新指令的语法为 [HAVOC X]，
    其中 [X] 是一个标识符。执行 [HAVOC X] 会为变量 [X] 赋予一个不确定的
    _'任意'_ 数值。例如，在执行完程序

      HAVOC Y;;
      Z ::= Y * 2

    后，[Y] 的值可以是任何数，而 [Z] 的值是 [Y] 的两倍（因此 [Z] 总是偶数）。
    注意，我们并未讨论输出值的_'概率'_，在执行完此非确定性代码后，
    会有无穷多可能的不同输出。

    某种意义上来说，[HAVOC] 所作用的变量大致相当于 C 之类的低级语言中的
    未初始化变量。经过了 [HAVOC] 的变量会保存一个固定但任意的数值。
    语言定义中的大部分非确定性来源于程序员对语言所做的选择不那么关心
    （好处是能让编译器选择更快的运行方式）。

    我们称这个心语言为_'Himp'_（“用 [HAVOC] 扩展的 Imp”）。 *)

Module Himp.

(** 为了形式化 Himp，我们首先在指令定义中增加一条从句。 *)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- 新增 *)

Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'HAVOC' l" :=
  (CHavoc l) (at level 60) : imp_scope.

(** **** 练习：2 星, standard (himp_ceval)  

    现在，我们必须扩展操作语义。前面我们已经提过了 [ceval] 关系的模版，
    指定了大步语义。为了形式化 [HAVOC] 指令的行为，我们还需要在 [ceval]
    的定义中添加哪些规则？ *)

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Open Scope imp_scope.
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
(* 请在此处解答 *)

  where "st =[ c ]=> st'" := (ceval c st st').
Close Scope imp_scope.

(** 作为合理性检查，以下断言对于你的定义来说应该是可证的： *)

Example havoc_example1 : empty_st =[ (HAVOC X)%imp ]=> (X !-> 0).
Proof.
(* 请在此处解答 *) Admitted.

Example havoc_example2 :
  empty_st =[ (SKIP;; HAVOC Z)%imp ]=> (Z !-> 42).
Proof.
(* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** 最后，我们重新定义和之前等价的指令： *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** 我们应用此定义来证明一些非确定性程序是否等价。 *)

(** **** 练习：3 星, standard (havoc_swap)  

    以下两个程序是否等价？ *)

Definition pXY :=
  (HAVOC X;; HAVOC Y)%imp.

Definition pYX :=
  (HAVOC Y;; HAVOC X)%imp.

(** 请证明你的想法。 *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard, optional (havoc_copy)  

    以下两个程序是否等价？ *)

Definition ptwice :=
  (HAVOC X;; HAVOC Y)%imp.

Definition pcopy :=
  (HAVOC X;; Y ::= X)%imp.

(** 请证明你的想法。（提示：你可能会用到 [assert] 的略。） *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(** 我们在这里使用的程序等价关系的定义对无限循环的程序来说有点复杂。因为
    [cequiv] 描述的是两个等价的程序在_'停机'_时输出的集合是相同的。然而，
    在像 Himp 这类带有非确定的语言中，有些程序总会停机，有些程序总会发散，
    还有些程序会非确定地在某些时候停机而在其它时候发散。
    以下练习的最后一部分展示了这种现象。
*)

(** **** 练习：4 星, advanced (p1_p2_term)  

    考虑一下指令： *)

Definition p1 : com :=
  (WHILE ~ (X = 0) DO
    HAVOC Y;;
    X ::= X + 1
  END)%imp.

Definition p2 : com :=
  (WHILE ~ (X = 0) DO
    SKIP
  END)%imp.

(** 直觉上来说，[p1] 和 [p2] 的停机行为相同：要么无限循环，要么以相同的状态开始，
    就在相同的状态下停机。我们可以用以下引理分别刻画 [p1] 和 [p2] 的停机行为： *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof. (* 请在此处解答 *) Admitted.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced (p1_p2_equiv)  

    使用这两个引理来证明 [p1] 和 [p2] 确实等价。 *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced (p3_p4_inequiv)  

    证明以下程序_'不等价'_（提示：当 [p3] 停机时 [Z] 的值是什么？当
    [p4] 停机时呢？） *)

Definition p3 : com :=
  (Z ::= 1;;
  WHILE ~(X = 0) DO
    HAVOC X;;
    HAVOC Z
  END)%imp.

Definition p4 : com :=
  (X ::= 0;;
  Z ::= 1)%imp.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, advanced, optional (p5_p6_equiv)  

    证明以下指令等价。（提示：正如我们之前提到的，我们为 Himp 定义的
    [cequiv] 只考虑了可能的停机配置的集合：对于两个拥有相同起始状态 [st]
    的程序而言，当且仅当二者可能的停机状态的集合相同时，二者才等价。
    若 [p5] 停机，那么最终状态应当是什么？反过来说，[p5] 总是会停机吗？） *)

Definition p5 : com :=
  (WHILE ~(X = 1) DO
    HAVOC X
  END)%imp.

Definition p6 : com :=
  (X ::= 1)%imp.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

End Himp.

(* ################################################################# *)
(** * 附加练习 *)

(** **** 练习：4 星, standard, optional (for_while_equiv)  

    此练习是 [Imp] 一章中可选练习 [add_for_loop] 的扩展，
    就是那个让你扩展出类似 C 风格的 [for] 循环指令的练习。请证明指令：

      for (c1 ; b ; c2) {
          c3
      }

    等价于：

       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
*)
(* 请在此处解答 

    [] *)

(** **** 练习：3 星, standard, optional (swap_noninterfering_assignments)  

    （提示：这里你需要 [functional_extensionality]。） *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced, optional (capprox)  

    在这个练习中我们定义了一个非对称的程序等价变形, 叫做
    _'程序近似（program approximation）'_。 当每个能让 [c1]
    停机的初始状态也能让 [c2] 在相同的状态下停机时，我们就说程序 [c1]
    _'近似与'_ 程序 [c2] 。下面是程序近似的形式化定义： *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** 例如，程序

  c1 = WHILE ~(X = 1) DO
         X ::= X - 1
       END

    近似于 [c2 = X ::= 1]，但是 [c2] 不近似于 [c1]，因为 [c1]
    不会在 [X = 0] 时停机，而 [c2] 会。如果两个程序互相近似，那么它们等价。 *)

(** 请找出两个程序 [c3] 和 [c4]，它们互不近似。 *)

Definition c3 : com
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Definition c4 : com
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* 请在此处解答 *) Admitted.

(** 找出一个程序 [cmin] 近似于所有别的程序。 *)

Definition cmin : com
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* 请在此处解答 *) Admitted.

(** 最后，再找出程序近似的一个非平凡的属性（当从左到右时）。 *)

Definition zprop (c : com) : Prop
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* 请在此处解答 *) Admitted.
(** [] *)

(* Fri Jul 19 00:33:13 UTC 2019 *)
