(** * Logic: Coq 中的逻辑系统 *)

(* TODO(OlingCat): 需要统一 claim、statement 的译法。 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

(**
    在前面的章节中，我们已经见过很多对事实的断言（即_'命题'_）
    以及如何用证据展示其正确性（即_'证明'_）的例子了。特别是，
    我们证明了大量形如 [e1 = e2] 的_'相等关系命题'_、形如 [P -> Q]
    的蕴含式、以及形如 [forall x, P x] 的量化命题。

    在深入细节之前，我们先来探讨一下 Coq 中数学表达式的地位。
    回忆一下，Coq 是一门拥有_'类型'_的语言，也就是说，一切有意义的
    表达式都具有一个相应的类型。逻辑表达也不例外，我们试图在 Coq
    中证明的一切语句都有名为 [Prop] 的类型，即_'命题类型'_。我们
    可以用 [Check] 指令来查看：  *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** 注意：_'所有'_语法形式良好的命题，无论是否为真，其类型均为 [Prop]。 *)

(** 简单来说，_'是'_一个命题与该命题_'可以证明'_是两回事。 *)

Check 2 = 2.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** 除了拥有类型之外，命题还是_'一等对象（First-Class Object）'_，
    即在 Coq 的世界中，我们可以像操作其它实体那样操作命题。 *)

(** 到目前为止，我们已经知道命题可以出现在 [Theorem]（还有 [Lemma] 以及
    [Example]）的声明中了。 *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** 不过命题还可以用在其它地方。例如，我们可以用 [Definition]
    为命题取名，就像为其它表达式取名一样。 *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** 之后我们可以在任何需要此命题的地方使用它们名字——例如，作为一个
    [Theorem] 声明中的断言： *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** 我们也可以写出_'参数化'_的命题 -- 也就是一个接受某些类型的参数，
    然后返回一个命题的函数。 *)

(** 例如，以下函数接受某个数字，返回一个命题断言该数字等于 3： *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** 在 Coq 中，返回命题的函数可以说是定义了其参数的_'性质'_。

    例如，以下（多态的）性质定义了常见的 _'单射函数'_ 的概念。 *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

(** 相等关系运算符 [=] 也是一个返回 [Prop] 的函数。

    表达式 [n = m] 只是 [eq n m] 的语法糖（它使用 Coq 的 [Notation]
    机制来定义）。 由于 [eq] 可被用于任何类型的元素，因此它也是多态的： *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** （注意我们写的是 [@eq] 而非 [eq]：[eq] 的类型参数 [A]
    是隐式声明的，因此我们需要关掉隐式参数以便看到 [eq] 的完整类型。） *)

(* ################################################################# *)
(** * 逻辑联结词 *)

(* ================================================================= *)
(** ** 合取 *)

(** 命题 [A] 与 [B] 的_'合取'_（即_'逻辑与'_）写作 [A /\ B]，表示一个
    [A] 与 [B] 均为真的断言。 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** 证明合取的命题通常使用 [split] 策略。它会分别为语句的两部分生成两个子目标： *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** 对于任意命题 [A] 和 [B]，如果我们假设 [A] 为真且 [B] 为真，
    那么就能得出 [A /\ B] 也为真的结论。 *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** 由于按照前提对某个目标应用定理会产生与该定理的前提一样多的子目标。
    因此我们可以应用 [and_intro] 来达到和 [split] 一样的效果。 *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** 练习：2 星, standard (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 以上就是证明合取语句的方法。要反过来使用，即_'使用'_合取前提来帮助证明时，
    我们会采用 [destruct] 策略。

    如果当前证明上下文中存在形如 [A /\ B] 的前提 [H]，那么
    [destruct H as [HA HB]] 将会从上下文中移除 [H] 并增加 [HA] 和 [HB]
    两个新的前提，前者断言 [A] 为真，而后者断言 [B] 为真。 *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* 课上已完成 *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 和往常一样，我们也可以在引入 [H] 的同时对其进行解构，
    而不必先引入然后再解构： *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 为什么我们要麻烦地将 [n = 0] 和 [m = 0] 这两个前提放一条合取语句中呢？
    完全可以用两条独立的前提来陈述此定理啊： *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 就此定理而言，两种方式都可以。不过理解如何证明合取前提非常重要，
    因为合取语句通常会在证明的中间步骤中出现，特别是在做大型开发的时候。
    下面是个简单的例子： *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* 课上已完成 *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** 另一种经常遇到合取语句的场景是，我们已经知道了 [A /\ B]，
    但在某些上下文中只需要 [A] 或者 [B]。此时以下引理会很有用： *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** 练习：1 星, standard, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 最后，我们有时需要重新排列合取语句的顺序，或者对多部分的合取语句进行分组。
    此时使用下面的交换律和结合律会很方便。 *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(** **** 练习：2 星, standard (and_assoc)  

    （在以下结合律的证明中，注意_'嵌套'_的 [intros] 模式是如何将
    [H : P /\ (Q /\ R)] 拆分为 [HP : P]、[HQ : Q] 和 [HR : R] 的。
    请从那里开始完成证明。） *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 顺便一提，中缀记法 [/\] 只是 [and A B] 的语法糖而已；
    [and] 是 Coq 中将两个命题合并成一个命题的运算符。 *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** 析取 *)

(** 另一个重要的联结词是_析取_，即两个命题的_'逻辑或'_：若 [A] 或 [B]
    二者之一为真，则 [A \/ B] 为真。（这中中缀记法表示 [or A B]，其中
    [or : Prop -> Prop -> Prop]。） *)

(** 为了在证明中使用析取前提，我们需要分类讨论，它与 [nat]
    或其它数据类型一样，都可以显示地通过 [destruct] 或隐式地通过 [intros]
    模式来拆分： *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* [Hn | Hm] 会隐式地对 [n = 0 \/ m = 0] 进行分类讨论 *)
  intros n m [Hn | Hm].
  - (* 在这里 [n = 0] *)
    rewrite Hn. reflexivity.
  - (* 在这里 [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** 相应地，要证明某个析取命题成立，我们需要证明其任意一边的命题成立。
    我们可以用 [left] 和 [right] 策略来选取命题。顾名思义，[left]
    会选取待析取证命题的左边，而 [right] 则会选取它的右边。
    下面是一种平凡的用法... *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ...而这个更有趣的例子则同时需要 [left] 和 [right]： *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* 课上已完成 *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** 练习：1 星, standard (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 假命题与否定 

    目前为止，我们主要都在证明某些东西是_'真'_的：加法满足结合律，
    列表的连接满足结合律，等等。当然，我们也关心_'否定'_的结果，
    即证明某些给定的命题_'不是'_真的。在 Coq 中，这样的否定语句使用否定运算符
    [~] 来表达。 *)

(** 为了理解否定背后的原理，我们需要回想一下[Tactics]一章中的_'爆炸原理'_。
    爆炸原理断言，当我们假设了矛盾存在时，就能推出任何命题。

    遵循这一直觉，我们可以可以将 [~ P]（即非 [P]）定义为 [forall Q, P -> Q]。

    不过 Coq 选择了稍有些不同（但等价）的做法，它将 [~ P] 定义为 [P -> False]，而
    [False] 是在标准库中特别定义的矛盾性命题。 *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** 由于 [False] 是个矛盾性命题，因此爆炸原理对它也适用。如果我们让 [False]
    进入到了证明的上下文中，可以对它使用 [destruct] 来完成任何待证目标。 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* 课上已完成 *)
  intros P contra.
  destruct contra.  Qed.

(** 拉丁文 _'ex falso quodlibet'_ 的字面意思是“从谬误出发，
    你能够证明任何你想要的”，这也是爆炸原理的另一个广为人知的名字。 *)

(** **** 练习：2 星, standard, optional (not_implies_our_not)  

    证明 Coq 对否定的定义蕴含前面提到的直觉上的定义： *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 不等性是十分常见的否定句的例子，，它有一个特别的记法 [x <> y]：

      Notation "x <> y" := (~(x = y)).
*)

(** 我们可以用 [not] 来陈述 [0] 和 [1] 是不同的 [nat] 元素： *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (** 性质 [0 <> 1] 就是 [~(0 = 1)]，即 [not (0 = 1)]，
      它会展开为 [(0 = 1) -> False]。（这里显式地用 [unfold not]
      展示了这一点，不过一般可以忽略。 *)
  unfold not.
  (** 要证明不等性，我们可以反过来假设其相等... *)
  intros contra.
  (** ... 然后从中推出矛盾。在这里，等式 [O = S O] 与构造子 [O] 和 [S]
      的不交性相矛盾，因此用 [discriminate] 就能解决它。 *)
  discriminate contra.
Qed.

(** 为了习惯用 Coq 处理否定命题，我们需要一些练习。
    即便你十分清楚为什么某个否定命题成立，但一下就找到让 Coq 理解的方式
    有点棘手。以下常见事实的证明留给你热身。 *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* 课上已完成 *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* 课上已完成 *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** 练习：2 星, advanced (double_neg_inf)  

    请写出 [double_neg] 的非形式化证明：

   _'定理'_：对于任何命题 [P] 而言，[P] 蕴含 [~~P]。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_double_neg_inf : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, advanced (informal_not_PNP)  

    请写出 [forall P : Prop, ~(P /\ ~P)] 的非形式化证明。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.
(** [] *)

(** 类似地，由于不等性包含一个否定，因此在能够熟练地使用它前也需要一些练习。
    这里有个有用的技巧：如果你需要证明某个目标不可能时（例如当前的目标陈述为
    [false = true]），请使用 [ex_falso_quodlibet] 将该目标转换为 [False]。
    如果在当前上下文中存在形如 [~P] 的假设（特别是形如 [x<>y] 的假设），
    那么此技巧会让这些假设用起来更容易些。 *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** 由于用 [ex_falso_quodlibet] 推理十分常用，因此 Coq 提供了内建的策略
    [exfalso]。 *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** 真值 *)

(** 除 [False] 外，Coq 的标准库中还定义了 [True]，一个明显真的命题。
    为了证明它，我们使用了预定义的常量 [I : True]： *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** 与经常使用的 [False] 不同，[True] 很少使用，因为它作为证明目标来说过于平凡，
    而作为前提又不携带任何有用的信息。 

    然而在使用条件从句定义复杂的 [Prop]，或者作为高阶 [Prop] 的参数时，
    它还是挺有用的。之后我们会看到 [True] 的这类用法。 *)

(* ================================================================= *)
(** ** 逻辑等价 *)

(** 联结词“当且仅当”用起来十分方便，它是两个蕴含式的合取，
    断言了两个命题拥有同样的真值。 *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* 课上已完成 *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* 课上已完成 *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** **** 练习：1 星, standard, optional (iff_properties)  

    参照上面对 [<->] 对称性（[iff_sym]）的证明，
    请证明它同时也有自反性和传递性。 *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** Coq 的某些策略会特殊对待 [iff] 语句，以此来避免操作某些底层的证明状态。
    特别来说，[rewrite] 和 [reflexivity] 不仅可以用于相等关系，还可用于
    [iff] 语句。为了开启此行为，我们需要导入一个 Coq 的库来支持它： *)

From Coq Require Import Setoids.Setoid.

(** 下面是一个简单的例子，它展示了这些策略如何使用 [iff]。
    首先，我们来证明一些基本的 [iff] 等价关系命题... *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** 现在我们可以用这些事实配合 [rewrite] 与 [reflexivity]
    对涉及等价关系的陈述给出流畅的证明了。以下是之前 [mult_0]
    包含三个变量的版本： *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** [apply] 策略也可以用在 [<->] 上。当给定一个等价关系命题作为
    [apply] 的参数时，它会试图应用正确的方向。 *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** 存在量化 *)

(** _'存在量化'_也是十分重要的逻辑联结词。我们说存在某个类型为 [T]
    的 [x]，使得某些性质 [P] 对于 [x] 成立，写作 [exists x : T, P]。
    和 [forall] 一样，如果 Coq 能从上下文中推断出 [x] 的类型，那么类型标注
    [: T] 就可以省略。*)

(** 为了证明形如 [exists x, P] 的语句，我们必须证明 [P] 对于某些特定的
    [x] 成立，这些特定的 [x] 被称作存在性的_'例证'_。证明分为两步：
    首先，我们调用 [exists t] 策略向 Coq 指出已经知道了使 [P]
    成立的例证 [t]，然后证明将所有出现的 [x] 替换成 [t] 的命题 [P]。 *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** 反之，如果我们的的上下文中有形如 [exists x, P] 的存在前提，
    可以将其解构得到一个例证 [x] 和一个陈述 [P] 对于 [x] 成立的前提。 *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* 课上已完成 *)
  intros n [m Hm]. (* 注意这里隐式使用了 [destruct] *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** 练习：1 星, standard, recommended (dist_not_exists)  

    请证明“[P] 对所有 [x] 成立”蕴含“不存在 [x] 使 [P] 不成立。”
    （提示：[destruct H as [x E]] 可以用于存在假设！） *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (dist_exists_or)  

    请证明存在量化对析取满足分配律。 *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 使用命题编程 *)

(** 我们学过的逻辑联结词为我们提供了丰富的用简单命题构造复杂命题的词汇。
    为了说明，我们来看一下如何表达“元素 [x] 出现在列表 [l] 中”这一断言。
    注意此性质有着简单的递归结构： 

       - 若 [l] 为空列表，则 [x] 无法在其中出现，因此性质“[x] 出现在 [l] 中”
         为假。 

       - 否则，若 [l] 的形式为 [x' :: l']，此时 [x] 是否出现在 [l] 中，
         取决于它是否等于 [x'] 或出现在 [l'] 中。 *)

(** 我们可以将此定义直接翻译成递归函数，它接受一个元素和一个列表，
    返回一个命题： *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** 当 [In] 应用于具体的列表时，它会被展开为一系列具体的析取式。 *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* 课上已完成 *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* 课上已完成 *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** （注意我们用空模式_'无视'_了最后一种情况。） *)

(** 我们也可证明关于 [In] 的更一般，更高阶的引理。

    注意，接下来会 [In] 被应用到一个变量上，只有当我们对它进行分类讨论时，
    它才会被展开： *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil，矛盾 *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** 虽然递归定义命题在某些情况下会很方便，但这种方式也有其劣势。特别是，
    这类命题会受到 Coq 对递归函数要求的限制，例如，在 Coq 中递归函数必须是
    “明显会终止”的。在下一章中，我们会了解如何_'归纳地'_定义命题，
    这是一种与之不同的技巧，有着其独特的优势和限制。 *)

(** **** 练习：2 星, standard (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (In_app_iff)  *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, recommended (All)  

    回忆一下，返回命题的函数可以视作对其参数_'性质'_的定义。例如，若
    [P] 的类型为 [nat -> Prop]，那么 [P n] 就陈述了性质 [P] 对 [n] 成立。

    以 [In] 作为参考，请写出递归函数 [All]，它陈述某个 [P] 对列表 [l]
    中的所有元素成立。为了确定你的定义是正确的，请在下方证明 [All_In] 引理。
    （当然，你的定义_'不应该'_为了通过测试就把 [All_In] 的左边复述一遍。 ） *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (combine_odd_even)  

    完成以下 [combine_odd_even] 函数的定义。它接受两个对数字成立的性质
    [Podd] 与 [Peven]，返回性质 [P] 使得当 [n] 为奇数时 [P n] 等价于 [Podd n]，
    否则等价于 [Peven n]。*)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** 为了测试你的定义，请证明以下事实： *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 对参数应用定理 *)

(** Coq 拥有一个不同于其它的证明助理（如 ACL2 和 Isabelle）的特性，
    即它将_'证明'_本身也作为一等对象。

    关于这一点有很多地方值得着墨，不过了解所有的细节对于使用 Coq 来说不是必须的。
    本节点到为止，深入的探讨参见 [ProofObjects] 和 [IndPrinciples]。 *)

(** 我们已经知道 [Check] 可以用来显式表达式的类型了，
    不过它还可以用来查找某个标识符所指代的定理。 *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** 在显示对定理 [plus_comm] 的_'陈述'_时，Coq 使用了与显示某项的_'类型'_一样的方式。
    这是为什么？ *)

(** 原因在于标识符 [plus_comm] 其实指代的是被称作_'证明对象'_的数据结构，
    它表示在命题 [forall n m : nat, n + m = m + n] 的真实性上建立的逻辑推导。
    此对象的类型_'就是'_其所证命题的陈述。 *)

(** 从直觉上来说，这很有道理，因为对定理的陈述说明了该定理可用来做什么，
    正如可计算对象的类型告诉了我们可以对它做什么。例如，若我们有一个类型为
    [nat -> nat -> nat] 的项，就可以给它两个 [nat] 作为参数并得到一个 [nat]。
    类似地，如果我们有一个类型为 [n = m -> n + n = m + m] 的对象，
    就能为它提供一个类型为 [n = m] 的“参数”并推导出 [n + n = m + m]。 *)

(** 从操作上来说，这种类比可以更进一步：由于定理可以作为函数应用到对应类型的前提上，
    我们就可以直接产生结论而不必使用中间出现的 [assert] 了。例如，假设我们想要证明以下结论： *)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** 乍看起来，我们似乎可以用 [plus_comm] 改写两次使两边匹配来证明它。
    然而问题是，第二次 [rewrite] 会抵消第一次的效果。 *)

Proof.
  (* 课上已完成 *)
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* 我们又回到了开始的地方... *)
Abort.

(** 利用我们已知的工具，修复它的一种简单方法是使用 [assert] 导出一个
    [plus_comm] 的特殊版本，这样我们就能用它按照预期来改写。 *)

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** 一种更优雅的方式是直接把我们想要实例化的参数应用到 [plus_comm] 上，
    正如我们将一个多态函数应用到类型参数上那样。 *)

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

(** 我们来展示另一个像函数那样使用定理或引理的例子。以下定理说明：
    任何包含元素的列表 [l] 一定非空。 *)

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

(** 有趣的地方是一个量化的变量（[x]）没有出现在结论（[l <> []]）中。 *)

(** 我们可以用此引理来证明 [x] 为 [42] 的特殊情况。直接用 [apply in_not_nil]
    会失败，因为它无法推出 [x] 的值。有一些方法可以绕开它... *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  (* 课上已完成 *)
  intros l H.
  Fail apply in_not_nil.
Abort.

(* [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* 显式地对 [x] 的值应用引理。 *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* 显式地对假设应用引理。 *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** 对于几乎所有将定理名作为参数的策略而言，你都可以“将定理作为函数”来使用。
    注意，定理应用与函数应用使用了同样的类型推导机制，所以你可以将通配符作为定理的参数，
    或者为定理声明默认的隐式前提。这些特性在以下证明中展示。（此证明如何工作的细节
    不必关心，这里的目标只是为了展示它的用途。） *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** 在以后的章节中我们将会看到更多这方面的例子。 *)

(* ################################################################# *)
(** * Coq vs. 集合论 *)

(** Coq 的逻辑核心，即_'归纳构造演算（Calculus of Inductive Constructions）'_系统，
    在很多重要的方面不同于数学家用来写下精确而严谨的证明的形式化系统。
    例如，在主流的纸笔数学家中使用最普遍的_'策梅洛-弗兰克尔集合论（ZFC）'_中，
    一个数学对象可同时属于不同的集合；而在 Coq 的逻辑中，一个项最多只属于一个类型。
    这些不同之处需要人们用稍微不同的方式来描述非形式化的数学概念，但总的来说，
    它们都是非常自然而易于使用的。例如，在 Coq 中我们一般不说某个自然数 [n]
    属于偶数集合，而是说 [even n] 成立，其中的 [even : nat -> Prop] 描述了偶数的性质。

    然而在某些情况下，将标准的数学论证翻译到 Coq 中会十分繁琐甚至是不可能的，
    除非我们引入新的公理来丰富其逻辑核心。作为本章的结尾，
    我们将探讨这两个世界之间最显著的区别。 *)

(* ================================================================= *)
(** ** 函数的外延性 *)

(** 目前为止我们所看见的相等关系断言基本上都只考虑了归纳类型的元素
    （如 [nat]、[bool] 等等）。然而由于 Coq 的相等关系运算符是多态的，
    因此它们并不是唯一的可能。特别是，我们可以写出宣称_'两个函数相等'_的命题： *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** 在一般的数学研究中，对于任意的两个函数 [f] 和 [g]，只要它们产生的结果相等，
    那么它们就被认为相等：

    (forall x, f x = g x) -> f = g

    这被称作_'函数的外延性原理'_。 *)

(** 不甚严谨地说，所谓“外延性”是指某个对象可观察到的行为。
    因此，函数的外延性就是指函数的标识完全由其行为来决定。
    用 Coq 的术语来说，就是函数的身份视其被应用后的结果而定。 *)

(** 函数的外延性并不在 Coq 的基本公理之内，因此某些“合理”的命题是不可证明的： *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* 卡住了 *)
Abort.

(** 然而，我们可以用 [Axiom] 指令将函数的外延性添加到 Coq 的核心逻辑系统中。 *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** 使用 [Axiom] 的效果与陈述一个定理并用 [Admitted] 跳过其证明相同，
    不过它会提醒读者这是一个公理，我们无需证明！*)

(** 现在我们可以在证明中调用函数的外延性了： *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** 当然，在为 Coq 添加公理时必须十分小心，因为这有可能会导致系统
    _'不一致'_，而当系统不一致的，任何命题都能在其中证明，包括 [False]
    和 [2+2=5]！

    不幸的是，并没有一种简单的方式能够判断添加某条公理是否安全：
    一般来说，确认任何一组公理的一致性都需要训练有素的专家付出艰辛的努力。

    然而，我们已经知道了添加函数外延性后的公理系统_'确实是'_一致的。 *)

(** 我们可以用 [Print Assumptions] 指令查看某个证明依赖的所有附加公理。 *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** 练习：4 星, standard (tr_rev_correct)  

    列表反转函数 [rev] 的定义有一个问题，它会在每一步都执行一次 [app]
    调用，而运行 [app] 所需时间与列表的大小线性渐近，也就是说 [rev]
    的时间复杂度与列表长度成平方关系。我们可以用以下定义来改进它： *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** 此版本是_'尾递归的'_，因为对函数自身的递归调用是需要执行的最后一步操作
    （即，在递归调用之后我们并不执行  [++] ）。
    一个足够好的编译器会对此生成十分高效的代码。请证明以下两个定义等价。 *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 命题与布尔值 *)

(** 我们已经知道在 Coq 中有两种编码逻辑事实的方式了，即使用_'布尔值'_
    （类型为 [bool]）和_'命题'_（类型为 [Prop]）。

    例如，我们可以通过以下两种方式来断言 [n] 为偶数： *)

(** [evenb n] 求值为 [true]： *)
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

(** 或者存在某个 [k] 使得 [n = double k]： *)
Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

(** 当然，如果二者刻画的偶数性描述的不是同一个自然数集合，那么会非常奇怪！
    幸运的是，我们确实可以证明二者相同... *)

(** 首先我们需要两个辅助引理。 *)
Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** 练习：3 星, standard (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* 提示：使用 [Induction.v] 中的 [evenb_S] 引理。  *)
  (* 请在此处解答 *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** 此定理说明，逻辑命题 [exists k, n = double k] 的真伪对应布尔计算 [evenb n]
    的真值。 *)

(** 类似地，以下两种 [n] 与 [m] 相等的表述等价：
      - (1) [n =? m] 值为 [true]；
      - (2) [n = m]。
    同样，二者的记法也等价。 *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

(** 然而，即便布尔值和某个断言的命题式在逻辑上是等价的，但它们在_'操作上'_
    也可能不一样。 *)

(** 在前面的偶数例子中，证明 [even_bool_prop] 的反向部分（即
    [evenb_double]，从命题到布尔表达式的方向）时，我们对
    [k] 进行了简单的归纳。而反方向的证明（即练习 [evenb_double_conv]）
    则需要一种聪明的一般化方法，因为我们无法直接证明
    [(exists k, n = double k) -> evenb n = true]。 *)

(** 对于这些例子来说，命题式的声明比与之对应的布尔表达式要更为有用，
    但并非总是如此。例如，我们无法在函数的定义中测试一般的命题是否为真，
    因此以下代码片段会被拒绝： *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq 会抱怨 [n = 2] 的类型是 [Prop]，而它想要一个 [bool]
    类型的元素（或其它带有两个元素的归纳类型）。此错误信息的原因与 Coq
    核心语言的_'计算性'_特质有关，即它能表达的所有函数都是可计算且完全的。
    这样设计的的原因之一是为了能从 Coq 开发的代码中提取出可执行程序。
    因此，在 Coq 中 [Prop] _'并没有'_一种通用的情况分析操作来确定
    任意给定的命题是否为真，一旦存在这种操作，我们就能写出不可计算的函数。

    尽管一般的不可计算性质无法表述为布尔计算，但值得注意的是，很多
    _'可计算的'_性质更容易通过 [Prop] 而非 [bool] 来表达，因为在 Coq
    中定义递归函数中会受到很大的限制。例如，下一章会展示如何用 [Prop]
    来定义“某个正则表达式可以匹配给定的字符串”这一性质。如果使用
    [bool] 来定义，就需要写一个真正的正则表达式匹配器了，这样会更加复杂，
    更难以理解，也更难以对它进行推理。

    另一方面，通过布尔值来陈述事实会带来一点重要的优势，即通过对 Coq
    中的项进行计算可以实现一些自动推理，这种技术被称为_'互映证明（Proof
    by Reflection）'_。考虑以下陈述： *)

Example even_1000 : exists k, 1000 = double k.

(** 对此命题而言，最直接的证明方式就是直接给出 [k] 的值。 *)

Proof. exists 500. reflexivity. Qed.

(** 而使用与之对应的布尔语句的证明则更加简单： *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** 有趣的是，由于这两种定义是等价的，因此我们无需显式地给出 500，
    而是使用布尔等价式来证明彼此： *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** 尽管此例的证明脚本的长度并未因此而减少，然而更大的证明通常可通过
    这种互映的方式来显著化简。举一个极端的例子，在用 Coq 证明著名的
    _'四色定理'_时，人们使用互映技巧将几百种不同的情况归约成了一个布尔计算。 *)

(** 另一点明显的不同是“布尔事实”的否定可以被直白地陈述并证明，
    只需翻转预期的布尔值结果即可。 *)

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* 课上已完成 *)
  reflexivity.
Qed.

(** 相反，命题的否定形式可能更难以掌握。 *)

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  (* 课上已完成 *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** 相等性补充了另一个例子。在涉及 [n] 和 [m] 的证明中，知道 [n =? m = true]
    通常没什么直接的帮助。然而如果我们将该语句转换为等价的 [n = m] 形式，
    则可利用该等式改写证明目标。
 *)

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* 课上已完成 *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** 我们不会详细地介绍互映技巧，然而对于展示布尔计算与一般命题的互补优势而言，
    它是个很好的例子。 *)

(** **** 练习：2 星, standard (logical_connectives)  

    以下引理将本章中讨论的命题联结词与对应的布尔操作关联了起来。 *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (eqb_neq)  

    以下定理为等价式 [eqb_eq] 的“否定”版本，
    在某些场景中使用它会更方便些（后面的章节中会讲到这方面的例子）。 *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (eqb_list)  

    给定一个用于测试类型为 [A] 的元素相等关系的布尔操作符 [eqb]，
    我们可以定义函数 [eqb_list] 来测试元素类型为 [A] 的列表的相等关系。
    请完成以下 [eqb_list] 函数的定义。要确定你的定义是否正确，请证明引理
    [eqb_list_true_iff]。 *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, recommended (All_forallb)  

    回忆一下[Tactics]一章中练习 [forall_exists_challenge] 的函数
    [forallb]： *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** 请证明以下定理，它将 [forallb] 与之前练习中 [All] 的性质关联了起来。 *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* 请在此处解答 *) Admitted.

(** 函数 [forallb] 是否还存在尚未被此规范捕获的重要性质？ *)

(* 请在此处解答 

    [] *)

(* ================================================================= *)
(** ** 经典逻辑 vs. 构造逻辑 *)

(** 我们已经知道了，在定义 Coq 函数时是无法判断命题 [P] 是否成立。
    然而_'证明'_也存在类似的限制！换句话说，以下推理原则即便符合直觉，
    不过在 Coq 中它是不可证明的： *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** 为了在操作上理解为何如此, 回忆一下，在证明形如 [P \/ Q]
    的陈述时，我们使用了 [left] 与 [right] 策略，它们能够有效地知道析取的哪边成立。
    然而在 [excluded_middle] 中，[P] 是被全称量化的_'任意'_命题，我们对它一无所知。
    我们没有足够的信息来选择使用 [left] 或 [right] 中的哪一个。就像 Coq
    因为缺乏信息而无法在函数内部机械地确定 [P] 是否成立一样。 *)

(** 然而，如果我们恰好知道 [P] 与某个布尔项互映，那么就能很轻易地知道它是否成立了：
    我们只需检查 [b] 的值即可。 *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** 特别来说，对于自然数 [n] 和 [m] 的 [n = m] 而言，排中律是成立的。 *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** 通用的排中律默认在 Coq 中并不可用，这一点或许很奇怪，毕竟，
    任何给定的断言都是非真即假的。尽管如此，不假设排中律的成立仍有其有限：
    Coq 中的陈述可以构造出比标准数学中同样陈述更强的断言。特别是，
    如果存在 [exists x, P x] 的 Coq 证明，那么我们就能直接给出一个使 [P x]
    得证的值 [x]。换言之，任何关于存在性的证明必定是_'构造性'_的。 *)

(** 像 Coq 一样不假设排中律成立的逻辑系统被称作_'构造逻辑'_。

    像 ZFC 这样更加传统的，排中律对于任何命题都成立的逻辑系统则被称作_'经典逻辑'_。 *)

(** 以下示例展示了为何假设排中律成立会导致非构造性证明：

    _'命题'_：存在无理数 [a] 和 [b] 使得 [a ^ b] 为有理数。

    _'证明'_：易知 [sqrt 2] 为无理数。若 [sqrt 2 ^ sqrt 2] 为有理数，
    那么可以取 [a = b = sqrt 2] 证明结束；否则 [sqrt 2 ^ sqrt 2] 为无理数。
    此时，我们可以取 [a = sqrt 2 ^ sqrt 2] 和 [b = sqrt 2]，因为
    [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2].  []

    看到发生什么了吗？我们使用排中律在不知道 [sqrt 2 ^ sqrt 2]
    是否为有理数的情况下就分别考虑了这两种情况！因此，我们知道了这样的
    [a] 和 [b] 存在，但却无法确切知道它们的值（至少使用此论据来说如此）。

    即便构造逻辑很有用，它也有自身的限制：存在很多容易用经典逻辑证明的命题，
    用构造证明会更加复杂，而对于某些已知的命题而言这样的构造性证明甚至不存在！
    幸运的是，排中律和函数外延性一样都是与 Coq 的逻辑系统兼容的，
    我们可以安全地将它作为公理添加到 Coq 中。然而，在本书中我们不必如此：
    我们所涉及的结构都可以完全用构造逻辑得到，所需的额外代价则微不足道。

    我们需要一定的实践才能理解哪些证明技巧不应在构造推理中使用，
    而其中的反证法尤为臭名昭著，因为它会导向非构造性证明。这里有个典型的例子：
    假设我们想要证明存在 [x] 具有某种性质 [P]，即存在 [P x]。我们先假设结论为假，
    也就是说 [~ exists x, P x]。根据此前提，不难推出 [forall x, ~ P x]。
    如果我们能够根据此中间事实得到矛盾，就能得到一个存在性证明而完全不必指出一个
    [x] 的值使得 [P x] 成立！

    从构造性的角度来看，这里存在着技术上的瑕疵，即我们试图通过对
    [~ ~ (exists x, P x)] 的证明来证明 [exists x, P x]。从以下练习中我们会看到，
    允许自己从任意陈述中去掉双重否定等价于引入排中律。因此，只要我们不引入排中律，
    就无法在 Coq 中编码此推理。 *)

(** **** 练习：3 星, standard (excluded_middle_irrefutable)  

    证明通用排中律公理与 Coq 的一致性需要复杂的推理，而且并不能在 Coq
    自身中进行。然而，以下定理蕴含了假设可判定性公理（即排中律的一个特例）
    成立对于任何_'具体的'_命题 [P] 而言总是安全的。之所以如此，
    是因为我们无法证明这类公理的否定命题。假如我们可以的话，就会同时有
    [~ (P \/ ~P)] 和 [~ ~ (P \/ ~P)]（因为根据以下练习， [P] 蕴含 [~ ~ P]），
    而这会产生矛盾。但因为我们不能，所以将 [P \/ ~P] 作为公理加入是安全的。 *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (not_exists_dist)  

    在经典逻辑中有这样一条定理，它断言以下两条命题是等价的：

    ~ (exists x, ~ P x)
    forall x, P x

    之前的 [dist_not_exists] 证明了此等价式的一个方向。有趣的是，
    我们无法用构造逻辑证明另一个方向。你的任务就是证明排中律蕴含此方向的证明。 *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, standard, optional (classical_axioms)  

    对于喜欢挑战的读者，以下练习来自于 Bertot 与 Casteran 所著的
    Coq'Art 一书中第 123 页。以下四条陈述的每一条，加上 [excluded_middle]
    可以认为刻画了经典逻辑。我们无法在 Coq 中证明其中的任意一条，
    不过如果我们希望在经典逻辑下工作的话，可以安全地将其中任意一条作为公理添加到
    Coq 中而不会造成不一致性。

    请证明所有五个命题都是等价的（这四个再加上 [excluded_middle]）。*)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* 请在此处解答 

    [] *)

(* Fri Jul 19 00:32:20 UTC 2019 *)
