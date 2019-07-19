(** * Imp: 简单的指令式程序 *)

(** 在本章中，我们会更加认真地看待如何用 Coq 来研究其它东西。
    我们的案例研究是一个名为 Imp 的_'简单的指令式编程语言'_，
    它包含了传统主流语言（如 C 和 Java）的一小部分核心片段。下面是一个用
    Imp 编写的常见数学函数：

       Z ::= X;;
       Y ::= 1;;
       WHILE ~(Z = 0) DO
         Y ::= Y * Z;;
         Z ::= Z - 1
       END
*)

(** 本章关注于如何定义 Imp 的_'语法'_和_'语义'_；_'《编程语言基础》
    （Programming Language Foundations）'_（_'《软件基础》'_第二卷）
    中的章节则发展了_'程序等价关系（Program Equivalence）'_并引入了
    _'霍尔逻辑（Hoare Logic）'_，它是一种广泛用于推理指令式程序的逻辑。 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From PLF Require Import Maps.

(* ################################################################# *)
(** * 算术和布尔表达式 *)

(** 我们会分三部分来展示 Imp：首先是_'算术和布尔表达式'_的核心语言，
    之后是用_'变量'_对表达式的扩展，最后是一个包括赋值、条件、串连和循环的
    _'指令'_语言。 *)

(* ================================================================= *)
(** ** 语法 *)

Module AExp.

(** 以下两个定义指定了算术和布尔表达式的_'抽象语法（Abstract Syntax）'_。 *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(** 在本章中，我们省略了大部分从程序员实际编写的具体语法到其抽象语法树的翻译
    -- 例如，它会将字符串 ["1 + 2 * 3"] 翻译成如下 AST：

      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

    可选的章节 [ImpParser] 中开发了一个简单的词法分析器和解析器，
    它可以进行这种翻译。你_'无需'_通过理解该章来理解本章，
    但如果你没有上过涵盖这些技术的课程（例如编译器课程），可能想要略读一下该章节。 *)

(** 作为对比，下面是用约定的 BNF（巴克斯-诺尔范式）文法定义的同样的抽象语法：

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | ~ b
        | b && b
*)

(** 与前面的 Coq 版本相对比...

       - BNF 是非形式化的 -- 例如，它给出了表达式表面上的语法的建议
         （例如加法运算符写作中缀的 [+]），而没有指定词法分析和解析的其它方面
         （如 [+]、[-] 和 [*] 的相对优先级，用括号来明确子表达式的分组等）。
         在实现编译器时，需要一些附加的信息（以及人类的智慧）
         才能将此描述转换成形式化的定义。

         Coq 版本则始终忽略了所有这些信息，只专注于抽象语法。

       - 反之，BNF 版本则更加清晰易读。它的非形式化使其更加灵活，
         在讨论和在黑板上书写时，它有很大的优势，
         此时传达一般的概念要比精确定下所有细节更加重要。

         确实，存在很多种类似 BNF 的记法，人们可以随意使用它们，
         而无需关心具体使用了哪种 BNF，因为没有必要：
         大致的理解是非常重要的。

    适应这两种记法都很有必要：非形式化的用语人类之间的交流，
    而形式化的则用于实现和证明。 *)

(* ================================================================= *)
(** ** 求值 *)

(** 对算术表达式进行_'求值（Evaluation）'_会得到数值。 *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** 同样，对布尔表达式求值会得到布尔值。 *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** 优化 *)

(** 我们尚未定义太多东西，不过从这些定义出发，已经能前进不少了。
    假设我们定义了一个接收算术表达式并对它稍微进行化简的函数，即将所有的
    [0 + e]（如 [(APlus (ANum 0) e]）化简为 [e]。 *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

(** 要保证我们的优化是正确的，可以在某些示例中测试它并观察其输出出否正确。 *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** 但如果要确保该优化的正确性，即优化后的表达式与原表达式的求值结果相同，
    那么我们应当证明它。 *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Coq 自动化 *)

(** 上一个证明中的大量重复很让人烦躁。无论算术表达式的语言，
    还是证明优化的可靠性明显都更加复杂，因此它会成为一个真正的问题。

    目前为止，我们所有的证明都只使用了一点趁手的 Coq 的策略，
    而它自动构造部分证明的强大功能则完全被忽略了。本节引入了这样的一些功能，
    而在下一章中我们会看到更多。要使用它们需要耗费点精力 --
    Coq 的自动化是个强大的工具 -- 不过它能让我们从无聊、重复、
    底层的细节中解放出来，专注于更加复杂的定义和更加有趣的性质。 *)

(* ================================================================= *)
(** ** 泛策略 *)

(** _'泛策略（Tacticals）'_是 Coq 中的术语，它表示一个接受其它策略作为参数的策略，
    当然，你愿意的话也可以把它称为“高阶策略”。 *)

(* ----------------------------------------------------------------- *)
(** *** [try] 泛策略 *)

(** 如果 [T] 是一个策略，那么 [try T] 是一个和 [T] 一样的策略，只是如果
    [T] 失败的话，[try T] 就会_'成功地'_什么也不做（而非失败）。*)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* 它和 [reflexivity] 做的一样。 *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* 和 [reflexivity] 失败时一样。 *)
  apply HP. (* 我们仍然可以换种方式来结束此证明。 *)
Qed.

(** 我们并没有真正的理由在像这样的手动证明中使用 [try]，不过在连同
    [;] 泛策略一起进行自动化证明时它会非常有用，接下来我们来展示它。 *)

(* ----------------------------------------------------------------- *)
(** *** [;] 泛策略（简单形式） *)

(** 在最常用的形式中，[;] 泛策略会接受两个策略作为参数。复合策略 [T;T']
    会在 [T] 生成的_'每个子目标'_中先执行 [T] 再执行 [T']。 *)

(** 例如，考虑以下平凡的引理： *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* 会产生两个执行过程相同的子目标...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** 我们可以用 [;] 泛策略来化简它： *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] 解构当前子目标 *)
  destruct n;
  (* 然后用 [simpl] 化简每个产生的子目标 *)
  simpl;
  (* 之后再对每个产生的子目标执行 [reflexivity] *)
  reflexivity.
Qed.

(** [try] 配合 [;] 一同使用，我们可以从之前证明中麻烦的重复里解脱出来。 *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* 大部分情况后面直接就是 IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... 不过剩下的情况 -- ANum 和 APlus -- 则不同： *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* 同样，大部分情况后面直接就是 IH： *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* 当 [e1 = ANum n] 时出现了有趣的情况，其中 [try...] 什么也不做。
       此时，我们需要解构 [n]（来确认优化是否应用）并用归纳假设来改写它。 *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

(** Coq 专家经常在像 [induction] 这样的策略之后使用这种“[...; try... ]”的习语，
    以便一次处理所有相似的情况。自然，在非形式化证明中也有同样的做法。
    例如，以下对该优化定理的非形式化证明与形式化证明的结构一致：

    _'定理'_：对于所有的算术表达式 [a]，

       aeval (optimize_0plus a) = aeval a.

    _'证明'_：对 [a] 进行归纳。大部分情况根据即可 IH 得证。其余情况如下：

      - 假设设对于某些 [n] 有 [a = ANum n] for some [n]。我们必须证明

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        这一点根据 [optimize_0plus] 的定义即可得证。

      - 假设对于某些 [a1] 和 [a2] 有 [a = APlus a1 a2]。我们必须证明

          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).

        考虑 [a1] 可能的形式。对于大部分的情况，[optimize_0plus]
        会对子表达式简单地递归调用自身并重建一个与 [a1] 形式相同的新表达式；
        在这些情况下，其结果根据 IH 即可得证。

        对某些 [n] 有 [a1 = ANum n] 是个有趣的情况。若 [n = 0]，则

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        而 [a2] 的 IH 正是所需的。另一方面，如果对于某些 [n'] 有 [n = S n']
        那么同样 [optimize_0plus] 会简单地递归调用自身，而其结果根据
        IH 即可得证。 [] *)

(** 然而，此证明仍然可以改进：第一种情况（[a = ANum n]）非常平凡，
    甚至比我们根据归纳假设化简的那个情况还要平凡，然而我们却把它完整地写了出来。
    为了更加清楚，最好把它去掉，然后在最上面说：“大部分情况可以立即得出，
    或直接从归纳假设得出。唯一有趣的情况是 [APlus]...”
    我们也可以在形式化证明中做出这种改进，方法如下： *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** [;] 泛策略（一般形式） *)

(** [;] 除了我们前面见到的简单形式 [T;T'] 外，还有种更一般的形式。
    如果 [T], [T1], ..., [Tn] 都是策略，那么

      T; [T1 | T2 | ... | Tn]

   就是一个首先执行 [T]，然后在 [T] 生成的第一个字母表中执行 [T1]，
   在第二个子目标中执行 [T2]，以此类推。

   因此，[T;T'] 只是一种当所有 [Ti] 为相同策略时的特殊记法，即，[T;T']
   是以下形式的简写：

      T; [T' | T' | ... | T']
*)

(* ----------------------------------------------------------------- *)
(** *** [repeat] 泛策略 *)

(** [repeat] 泛策略接受另一个测略并重复应用它直至失败。以下示例用
    [repeat] 证明了 [10] 在一个长列表中。 *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** 策略 [repeat T] 永远不会失败：如果策略 [T] 并未应用到原始目标上，
    那么 [repeat] 仍然会成功而不改变原始目标（即，它重复了零次）。 *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** 策略 [repeat T] 应用 [T] 的次数也没有任何上界。如果 [T] 策略总是成功，
    那么重复 [T] 会永远循环（例如 [repeat simpl] 会一直循环，因为 [simpl]
    总是会成功）。虽然 Coq 的主语言 Gallina 中的求值保证会终止，
    然而策略却不会！然而这并不会影响 Coq 的逻辑一致性，因为 [repeat]
    和其它策略的工作就是指导 Coq 去构造证明；如果构造过程发散（即不停机），
    那就意味着我们构造证明失败，而非构造出了错误的证明。 *)

(** **** 练习：3 星, standard (optimize_0plus_b_sound)  

    由于 [optimize_0plus] 变换不会改变 [aexp] 的值，
    因此我们可以将它应用到所有出现在 [bexp] 中的 [aexp] 上而不改变
    [bexp] 的值。请编写一个对 [bexp] 执行此变换的函数，并证明它的可靠性。
    利用我们刚学过的泛策略来构造一个尽可能优雅的证明。 *)

Fixpoint optimize_0plus_b (b : bexp) : bexp
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard, optional (optimize)  

    _'设计练习'_：[optimize_0plus] 函数只是众多算术和布尔表达式优化的方法之一。
    请编写一个更加聪明的优化器并证明它的正确性。（最容易的方法就是从小处着手：
    一开始只添加单个简单的优化并证明它的正确性，然后逐渐增加其它更有趣的优化。） *)

(* 请在此处解答 

    [] *)

(* ================================================================= *)
(** ** 定义新的策略记法 *)

(** Coq 还提供了几种对策略脚本进行“编程”的方式。

    - 下面展示的 [Tactic Notation] 习语给出了定义“简写策略”的简便方式，
      它将多个策略封装成单条指令。

    - 对于更加复杂的编程，Coq 提供了内建的 [Ltac] 语言，
      它带有可以检查和修改证明状态的原语。由于详情太过复杂，这里不便展开
      （[Ltac] 通常也被认为不是 Coq 的设计中最美妙的部分！），
      你可以在参考手册和其它关于 Coq 的书中找到它，Coq 的标准库中有很多
      [Ltac] 定义的例子，你也可以参考它们。

    - 还有 OCaml 的 API，它可以构建从底层访问 Coq 内部结构的策略，
      不过普通 Coq 用于很少需要麻烦它。

    [Tactic Notation] 机制是最易于掌握的，它为很多用途提供了强大的能力。
    下面就是个例子。 *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** 这定义了一个新的名为 [simpl_and_try] 的泛策略，它接受一个策略 [c]
    作为参数，其定义等价于策略 [simpl; try c]。现在在证明中写
    “[simpl_and_try reflexivity.]”和写“[simpl; try reflexivity.]”是一样的。 *)

(* ================================================================= *)
(** ** [omega] 策略 *)

(** [omega] 实现了一种决策过程，它是名为_'Presburger 算术'_的一阶逻辑的一个子集。
    它基于启发自 William Pugh [Pugh 1991] (in Bib.v) 的 Omega 算法。

    如果证明目标是由以下元素构成的式子：

      - 数值常量、加法（[+] 和 [S]）、减法（[-] 和 [pred]）以及常量乘法
        （这就是 Presburger 算术的构成要素）

      - 相等关系（[=] 和 [<>]）和序（[<=]）

      - 逻辑连结 [/\]、[\/]、[~] 和 [->]

    那么调用 [omega] 要么会解决该证明目标，要么就会失败，这意味着该目标为假
    （目标_'不满足'_此形式也会失败。） *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** （注意本文件顶部 [From Coq Require Import omega.Omega.]。）*)

(* ================================================================= *)
(** ** 更多方便的策略 *)

(** 最后，下面列出一些方便的其它技巧。

     - [clear H]：从上下文中删除前提 [H]。

     - [subst x]：对于变量 [x]，在上下文中查找假设 [x = e] 或 [e = x]，
       将整个上下文和当前目标中的所有 [x] 替换为 [e] 并清除该假设。

     - [subst]：替换掉_'所有'_形如 [x = e] 或 [e = x] 的假设（其中 [x] 为变量）。

     - [rename... into...]：更改证明上下文中前提的名字。例如，
       如果上下文中包含名为 [x] 的变量，那么 [rename x into y]
       就会将所有出现的 [x] 重命名为 [y]。

     - [assumption]：尝试在上下文中查找完全匹配目标的前提 [H]。
       如果找到了，那么其行为与 [apply H] 相同。

     - [contradiction]：尝试在当前上下文中查找逻辑等价于 [False] 的前提 [H]。
      如果找到了，就解决该目标。

     - [constructor]：尝试在当前环境中的 [Inductive]
       定义中查找可用于解决当前目标的构造子 [c]。如果找到了，那么其行为与
       [apply c] 相同。

    我们之后会看到所有它们的例子。 *)

(* ################################################################# *)
(** * 求值作为关系 *)

(** 我们已经展示了用 [Fixpoint] 定义的函数 [aeval] 和 [beval]。
    另一种通常更加灵活的思考求值的方式，就是把它当做表达式与其值的_'关系'_。
    （译注：求值关系不满足对称性，因为它是有方向的。）
    这会自然地导出如下这种算术表达式的 [Inductive] 定义... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.

(* A small notational aside. We would previously have written the
   definition of [aevalR] like this, with explicit names for the
   hypotheses in each case: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

(** Instead, we've chosen to leave the hypotheses anonymous, just
    giving their types.  This style gives us less control over the
    names that Coq chooses during proofs involving [aevalR], but it
    makes the definition itself quite a bit lighter. *)

End TooHardToRead.

(** 如果 [aevalR] 有中缀记法的话会很方便。我们用 [e \\ n]
    表示算术表达式 [e] 求值为 [n]。 *)

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(** 实际上，Coq 提供了一种在 [aevalR] 自身内使用此记法的方式。
    这样可以避免在进行涉及 [e \\ n] 形式的证明时，必须向前引用
    [aevalR e n] 形式的定义的情况，从而减少混淆。

    具体做法是，我们先“保留”该记法，然后在给出定义的同时声明它的意义。*)

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** 推理规则的记法 *)

(** 在非形式化的讨论中，将 [aevalR] 和类似的关系写成更加易读的
    _'推理规则（Inference Rule）'_的图像形式会十分方便，
    其中横线上方的前提证明了横线下方的结论是正确的（我们已经在
    [IndProp] 一章中见过它们了）。 *)

(** 例如，构造子 [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...的推理规则写作：

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                (E_APlus)
                         APlus e1 e2 \\ n1+n2
*)

(** 形式上来说，推理规则没什么深刻的含义：它们只是蕴含关系。
    你可以将右侧的规则名看做构造子名，将横线上每个前提见的换行（以及横线本身）
    看做 [->]。规则中涉及的所有变量（如 [e1]、[n1] 等）从一开始都是全称量化的。
    （这种变量通常称为_'元变量（Metavariables）'_，以区别于我们在语言中定义的变量。
    目前，我们的算术表达式中还不包含变量，不过之后会加入它们。）
    整个规则集合都被认为包裹在 [Inductive] 声明中。在非正式的叙述中，
    这一点要么会忽略，要么会通过类似于“令 [aevalR] 为对以下规则封闭的最小关系...”
    的句子来表述。 *)

(** 例如，[\\] 是对以下规则封闭的最小关系：

                             -----------                               (E_ANum)
                             ANum n \\ n

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2

                               e1 \\ n1
                               e2 \\ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 \\ n1-n2

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 \\ n1*n2
*)

(** **** 练习：1 星, standard, optional (beval_rules)  

    下面是 Coq 中 [beval] 函数的定义：

  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => (aeval a1) =? (aeval a2)
    | BLe a1 a2   => (aeval a1) <=? (aeval a2)
    | BNot b1     => negb (beval b1)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.

    请用推理规则记法将布尔求值的定义写成关系的形式。 *)
(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_beval_rules : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 定义的等价关系 *)

(** 求值的函数式定义与关系式定义之间的一致性证明非常直观： *)

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** 我们可以利用泛策略将此证明缩减到很短。 *)

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* 课上已完成 *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** 练习：3 星, standard (bevalR)  

    用和 [aevalR] 同样的方式写出关系 [bevalR]，并证明它等价于 [beval]。 *)

Inductive bevalR: bexp -> bool -> Prop :=
(* 请在此处解答 *)
.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

End AExp.

(* ================================================================= *)
(** ** 计算式定义与关系式定义 *)

(** 对于算术和布尔表达式求值的定义方式而言，函数式和关系式二者均可，
    选择哪种主要取决于品味。

    然而在某些情况下，求值的关系式定义比函数式定义要更好。  *)

Module aevalR_division.

(** 例如，假设我们想要用除法来扩展算术运算： *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- 新增 *)

(** 扩展 [aeval] 的定义来处理此讯算并不是很直观（我们要返回什么作为
    [ADiv (ANum 5) (ANum 0)] 的结果？）。然而扩展 [aevalR] 却很直观。*)

Reserved Notation "e '\\' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

(** 假设我们想要用非确定性的数值生成器 [any] 来扩展算术运算，
    该生成器会在求值时产生任何数。（注意，这不同于在所有可能的数值中作出
    _'概率上的'_选择 -- 我们没有为结果指定任何具体的概率分布，只是说了
    _'可能的结果'_。） *)

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** 同样，扩展 [aeval] 会很棘手，因为现在的求值_'并不是'_一个从表达式到数值的确定性函数，
    而扩展 [aevalR] 则无此问题... *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny \\ n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** 这时你可能会问：默认情况下应该使用哪种风格？
    我们刚看到的例子表明关系式的定义反而比函数式的更加有用。
    对于这种定义的东西不太容易用函数表达，或者确实_'不是'_函数的情况来说，
    明显别无选择。但如果两种风格均可行呢？

    关系式定义的一个优点是，它们会更优雅，更容易理解。

    另一个优点是，Coq 会根据 [Inductive] 定义自动生成不错的反演函数和归纳法则。 *)

(** 另一方面，函数式定义通常会更方便：
     - 函数的定义是确定性的，且在所有参数上定义；而对于关系式定义来说，
       我们需要这些性质时必须显式地证明它们。
     - 有了函数，我们还可以利用 Coq 的计算机制在证明过程中简化表达式。

    此外，函数还可以直接从 Gallina“提取”出 OCaml 或 Haskell 的可执行代码。 *)

(** 最终，选择视具体情况而定，或者只是品味问题。确实，在大型的 Coq
    开发中，经常可以看到一个定义同时给出了函数式和关系式_'两种'_风格，
    加上一条陈述了二者等价的引理，以便在之后的证明中能够在这两种视角下随意切换。 *)

(* ################################################################# *)
(** * 带变量的表达式 *)

(** 让我们回到 Imp 的定义上来。接下来我们要为算术和布尔表达式加上变量。
    为简单起见，我们会假设所有变量是都全局的，且它们只保存数值。 *)

(* ================================================================= *)
(** ** 状态 *)

(** 由于需要查找变量来获得它们的具体值，因此我们重用了 [Maps]
    一章中的映射。我们在 Imp 中以 [string] 作为变量的类型。

    _'机器的状态'_（简称_'状态'_）表示程序执行中某一时刻_'所有变量'_的值。 *)

(** 虽然任何给定的程序只会涉及有限数量的变量，不过为简单起见，
    我们假设状态为_'所有的'_变量定义。状态会捕获内存中所有的信息。
    对 Imp 程序而言，由于每个变量都存储了一个自然数，
    因此我们可以将状态表示为一个从字符串到 [nat] 的映射，并且用 [0]
    作为存储中的默认值。对于更复杂的编程语言，状态会有更多结构。 *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** 语法  *)

(** 我们只需为之前的算术表达式再加一个构造子就能添加变量： *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x :  string)             (* <--- 新增 *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** 为几个变量名定义简单记法能让示例更加易读： *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** （这种命名程序变量的约定（[X]、[Y]、[Z]）
    与我们之前使用大写字母表示类型有点冲突。由于我们在本章中开发 Imp
    时没怎么使用多态，所以这种重载应该不会产生混淆。） *)

(** [bexp] 的定义现在除了引用了新的 [aexp] 之外并未更改： *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** 记法 

    要让 Imp 程序更易读写，我们引入了一些记法和隐式转换（Coercion）。

    你无需理解以下声明具体做了些什么。简言而之，Coq 中的 [Coercion]
    声明规定了一个函数（或构造子）可以被类型系统隐式地用于将一个输入类型的值
    转换成输出类型的值。例如，[AId] 的转换声明在需要一个 [aexp]
    时直接使用普通的字符串，该字符串会被隐式地用 [AId] 来包装。 *)

(** 下列记法在具体的_'记法作用域'_中声明，以避免与其它符号相同的解释相冲突。
    同样，你暂时也无需理解其中的细节，但要意识到到我们为 [+]、[-]、[*]、[=]、[<=]
    等运算符定义了_'新的'_解释十分重要。 *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

(** 现在我们可以用 [3 + (X * 2)] 来代替 [APlus 3 (AMult X 2)] 了，同样可以用
    [true && !(X <= 4)] 来代替 [BAnd true (BNot (BLe X 4))]。 *)

Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.

(** 强制转换有一点不便之处，即它会略微提高人类推导表达式类型的难度。
    如果你感到有点困惑，请用 [Set Printing Coercions] 来查看具体发生了什么。 *)

Set Printing Coercions.

Print example_bexp.
(* ===> example_bexp = bool_to_bexp true && ~ (AId X <= ANum 4) *)

Unset Printing Coercions.

(* ================================================================= *)
(** ** 求值 *)

(** 算术和布尔求值器被扩展成以很显然的方式来处理变量，
    它接受一个状态作为额外的参数： *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- 新增 *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(** 我们为具体状态的全映射声明具体的记法，即使用 [(_ !-> 0)] 作为空状态。 *)

Definition empty_st := (_ !-> 0).

(** 现在我们可以为“单例状态（singleton state）”添加新的记法了，
    即只有一个绑定到值的变量。 *)
Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X <= 4))%imp
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * 指令 *)

(** 现在我们可以定义 Imp _'指令（Command）'_（有时称作_'语句（Statement）'_）
    的语法和行为了。 *)

(* ================================================================= *)
(** ** 语法 *)

(** 指令 [c] 可以用以下 BNF 文法非形式化地描述。

     c ::= SKIP | x ::= a | c ;; c | TEST b THEN c ELSE c FI
         | WHILE b DO c END

    （为了能够使用 Coq 的记法机制来定义 Imp 语法，我们选择了这种略尴尬的具体语法。
    具体来说，我们使用了 [TEST] 来避免与表中库中的 [if] 记法相冲突。） 
    例如，下面是用 Imp 编写的阶乘：

     Z ::= X;;
     Y ::= 1;;
     WHILE ~(Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   当此指令终止后，[Y] 会保存初始值 [X] 的阶乘。 *)

(** 下面是指令的抽象语法的形式化定义： *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** 至于表达式，我们可以用一些 [Notation] 声明来让 Imp 程序的读写更加方便。 *)

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

(** 例如，下面是个阶乘函数，写成 Coq 的形式化定义： *)

Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

(* ================================================================= *)
(** ** 脱糖记法 *)

(** Coq 为管理日益复杂的工作对象提供了丰富的特性，例如隐式转换和记法。
    然而，过度使用它们会产生繁杂的语法。为了教学，我们通常会用以下命令来
    “关闭”这些特性以获得对事物更加本质的描述：

    - [Unset Printing Notations]（用 [Set Printing Notations] 撤销）
    - [Set Printing Coercions]（用 [Unset Printing Coercions] 撤销）
    - [Set Printing All]（用 [Unset Printing All] 撤销）

    这些命令也可在证明过程中详述当前目标和上下文。 *)

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAss Z X)
        (CSeq (CAss Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAss Y (AMult Y Z))
                            (CAss Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   (Z ::= AId X;;
   Y ::= ANum 1;;
   WHILE ~ (AId Z = ANum 0) DO
     Y ::= AId Y * AId Z;;
     Z ::= AId Z - ANum 1
   END)%imp
       : com *)
Unset Printing Coercions.

(* ================================================================= *)
(** ** [Locate] 命令 *)

(* ----------------------------------------------------------------- *)
(** *** 查询记法 *)

(** 当遇到未知记法时，可使用 [Locate] 后跟一个包含其符号的_'字符串'_
    来查看其可能的解释。 *)
Locate "&&".
(* ===>
   Notation "x && y" := andb x y : bool_scope (default interpretation) *)

Locate ";;".
(* ===>
   Notation "c1 ;; c2" := CSeq c1 c2 : imp_scope (default interpretation) *)

Locate "WHILE".
(* ===>
   Notation "'WHILE' b 'DO' c 'END'" := CWhile b c : imp_scope
   (default interpretation) *)

(* ----------------------------------------------------------------- *)
(** *** 查询标识符 *)

(** 当以标示符使用 [Locate] 时，它会打印作用域中同名的所有值的完成路径。
    它很适合解决由变量覆盖所引起的问题。 *)
Locate aexp.
(* ===>
   Inductive Top.aexp
   Inductive Top.AExp.aexp
     (shorter name to refer to it in current context is AExp.aexp)
   Inductive Top.aevalR_division.aexp
     (shorter name to refer to it in current context is aevalR_division.aexp)
   Inductive Top.aevalR_extended.aexp
     (shorter name to refer to it in current context is aevalR_extended.aexp)
*)

(* ================================================================= *)
(** ** 更多示例 *)

(** 赋值： *)

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

(* ----------------------------------------------------------------- *)
(** *** 循环 *)

Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END)%imp.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** 无限循环： *)

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

(* ################################################################# *)
(** * 求值指令 *)

(** 接下来我们要定义对 Imp 指令进行求值是什么意思。
    [WHILE] 未必会终止的事实让定义它的求值函数有点棘手... *)

(* ================================================================= *)
(** ** 求值作为函数（失败的尝试） *)

(** 下面是一次为指令定义求值函数的尝试，我们忽略了 [WHILE] 的情况。 *)

(** 为了在模式匹配中使用记法，我们需要以下声明。 *)
Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* 假装能用 *)
  end.
Close Scope imp_scope.

(** 在 OCaml 或 Haskell 这类传统的函数式编程语言中，我们可以像下面这样添加
    [WHILE] 的情况：

        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | WHILE b DO c END =>
                if (beval st b)
                  then ceval_fun st (c ;; WHILE b DO c END)
                  else st
          end.

    Coq 会拒绝这种定义（“Error: Cannot guess decreasing argument of fix”，
    错误：无法猜测出固定的递减参数），因为我们想要定义的函数并不保证终止。
    确实，它并不_'总是会终止'_：例如，[ceval_fun] 函数应用到上面的 [loop]
    程序的完整版本永远不会终止。由于 Coq 不仅是一个函数式编程语言，
    还是个逻辑一致的语言，因此任何潜在的不可终止函数都会被拒绝。下面是一个
    （无效的）程序，它展示了如果 Coq 允许不可终止的递归函数的话会产生什么错误：

         Fixpoint loop_false (n : nat) : False := loop_false n.

    也就是说，像 [False] 这样的假命题可以被证明（[loop_false 0] 会是 [False]
    的一个证明），这对于 Coq 的逻辑一致性来说是个灾难。

    由于它对于所有的输入都不会终止，因此 [ceval_fun] 无法在 Coq 中写出
    -- 至少需要一些技巧和变通才行（如果你对此好奇的话请阅读
    [ImpCEvalFun] 一章）。 *)

(* ================================================================= *)
(** ** 求值作为一种关系 *)

(** 下面是一种更好的方法：将 [ceval] 定义成一种_'关系'_而非一个_'函数'_
    -- 即，用 [Prop] 而非用 [Type] 来定义它，和我们前面对 [aevalR] 做的那样。 *)

(** 这是一个非常重要的更改。除了能将我们从尴尬的变通中解放出来之外，
    它还给我们的定义赋予了更多的灵活性。例如，如果我们要为该语言添加更多像
    [any] 这样非确定性的特性，我们需要让求值的定义也是非确定性的 --
    即，它不仅会有不完全性，甚至还可以不是个函数！ *)

(** 我们将使用记法 [st =[ c ]=> st'] 来表示 [ceval] 这种关系：[st =[ c ]=> st']
    表示在开始状态 [st] 下启动程序并在结束状态 [st'] 下产生结果。它可以读作：
    “[c] 将状态 [st] 变成 [st']”。 *)

(* ----------------------------------------------------------------- *)
(** *** 操作语义 *)

(** 下面是求值的非形式化定义，为了可读性表示成推理规则：

                           -----------------                             (E_Skip)
                           st =[ SKIP ]=> st

                           aeval st a1 = n
                   --------------------------------                       (E_Ass)
                   st =[ x := a1 ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                            (E_Seq)
                         st =[ c1;;c2 ]=> st''

                          beval st b1 = true
                           st =[ c1 ]=> st'
                ---------------------------------------                (E_IfTrue)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b1 = false
                           st =[ c2 ]=> st'
                ---------------------------------------               (E_IfFalse)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b = false
                    -----------------------------                  (E_WhileFalse)
                    st =[ WHILE b DO c END ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ WHILE b DO c END ]=> st''
                  --------------------------------                  (E_WhileTrue)
                  st  =[ WHILE b DO c END ]=> st''
*)

(** 下面是它的形式化定义。请确保你理解了它是如何与以上推理规则相对应的。 *)

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

  where "st =[ c ]=> st'" := (ceval c st st').

(** 将求值定义成关系而非函数的代价是，我们需要自己为某个程序求值成某种结束状态_'构造证明'_，
    而不能只是交给 Coq 的计算机制去做了。 *)

Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* 我们必须提供中间状态 *)
  apply E_Seq with (X !-> 2).
  - (* 赋值指令 *)
    apply E_Ass. reflexivity.
  - (* if 指令 *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

(** **** 练习：2 星, standard (ceval_example2)  *)
Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (pup_to_n)  

    写一个 Imp 程序对从 [1] 到 [X] 进行求值（包括：将 [1 + 2 + ... + X]) 赋予变量 [Y]。
   证明此程序对于 [X] = [2] 会按预期执行（这可能比你预想的还要棘手）。 *)

Definition pup_to_n : com
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 求值的确定性 *)

(** 将求值从计算式定义换成关系式定义是个不错的改变，
    因为它将我们从求值必须是全函数的人工需求中解放了出来。不过这仍然引发了一个问题：
    求值的第二种定义真的是一个偏函数吗？从同样的 [st]
    开始, 我们是否有可能按照不同的方式对某个指令 [c] 进行求值，
    从而到达两个不同的输出状态 [st'] 和 [st'']?

    实际上这不可能发生，因为 [ceval] _'确实'_是一个偏函数： *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* 对断言的证明 *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue，b1 求值为 true *)
      apply IHE1. assumption.
  - (* E_IfTrue，b1 求值为 false（矛盾） *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 求值为 true（矛盾） *)
    rewrite H in H5. discriminate H5.
  - (* E_IfFalse，b1 求值为 false *)
      apply IHE1. assumption.
  - (* E_WhileFalse，b1 求值为 false *)
    reflexivity.
  - (* E_WhileFalse，b1 求值为 true（矛盾） *)
    rewrite H in H2. discriminate H2.
  - (* E_WhileTrue, b1 求值为 false（矛盾） *)
    rewrite H in H4. discriminate H4.
  - (* E_WhileTrue，b1 求值为 true *)
      assert (st' = st'0) as EQ1.
      { (* 对断言的证明 *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * 对 Imp 进行推理 *)

(** 我们会在_'《编程语言基础》'_中更加深入地探讨对 Imp 程序进行推理的系统性技术，
    不过目前只根据定义就能做很多工作。本节中会我们会探讨一些实例。 *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** 反转 [Heval] 实际上会强制让 Coq 展开 [ceval] 求值的一个步骤 --
      由于 [plus2] 是一个赋值，因此这种情况揭示了 [st'] 一定是 [st]
      通过新的值 [X] 扩展而来的。 *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** 练习：3 星, standard, recommended (XtimesYinZ_spec)  

    叙述并证明 [XtimesYinZ] 的规范（Specification）。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, standard, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef
           eqn:Heqloopdef.

  (** 归纳讨论假设“[loopdef] 会终止”之构造，其中多数情形的矛盾显而易见，
      可用 [discriminate] 一步解决。 *)

  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (no_whiles_eqv)  

    考虑以下函数： *)

Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.
Close Scope imp_scope.

(** 此断言只对没有 [WHILE] 循环的程序产生 [true]。请用 [Inductive]
    写出一个性质 [no_whilesR] 使得 [no_whilesR c] 仅当 [c] 是个没有
    [WHILE] 循环的程序时才可以证明。之后证明它与 [no_whiles] 等价。 *)

Inductive no_whilesR: com -> Prop :=
 (* 请在此处解答 *)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard (no_whiles_terminating)  

    不涉及 [WHILE] 循环的 Imp 程序一定会终止。请陈述并证明定理
    [no_whiles_terminating] 来说明这一点。 

    按照你的偏好使用 [no_whiles] 或 [no_whilesR]。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * 附加练习 *)

(** **** 练习：3 星, standard (stack_compiler)  

    旧式惠普计算器的编程语言类似于 Forth 和 Postscript，而其抽象机器类似于
    Java 虚拟机，即所有对算术表达式的求值都使用_'栈'_来进行。例如，表达式

      (2*3)+(3*(4-2))

   会被写成

      2 3 * 3 4 2 - * +

   的形式，其求值过程如下（右侧为被求值的程序，左侧为栈中的内容）：

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  此练习的目的在于编写一个小型编译器，它将 [aexp] 翻译成栈机器指令。

  栈语言的指令集由以下指令构成：
     - [SPush n]：将数 [n] 压栈。
     - [SLoad x]：从存储中加载标识符 [x] 并将其压栈。
     - [SPlus]：  从栈顶弹出两个数，将二者相加，并将其结果压栈。
     - [SMinus]： 类似，不过执行减法。
     - [SMult]：  类似，不过执行乘法。 *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** 请编写一个函数对栈语言程序进行求值。它应当接受一个状态、
    一个表示为数字列表的栈（栈顶项在表头），以及一个表示为指令列表的程序作为输入，
    并在程序执行后返回该栈。请在以下示例中测试你的函数。

    注意，当栈中的元素少于两个时，规范并未指定 [SPlus]、[SMinus] 或 [SMult] 指令的行为。
    从某种意义上说，这样做并无必要，因为我们的编译器永远不会产生这种畸形的程序。 *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* 请在此处解答 *) Admitted.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* 请在此处解答 *) Admitted.

(** 接下来请编写一个将 [aexp] 编译成栈机器程序的函数。运行此程序的效果
    应当和将该表达式的值压入栈中一致。 *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** 在定义完 [s_compile] 之后，请证明以下示例来测试它是否起作用。 *)

Example s_compile1 :
  s_compile (X - (2 * Y))%imp
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced (stack_compiler_correct)  

    现在我们将证明在之前练习中实现的编译器的正确性。记住当栈中的元素少于两个时，
    规范并未指定 [SPlus]、[SMinus] 或 [SMult] 指令的行为。
    （为了让正确性证明更加容易，你可能需要返回去修改你的实现！）

    请证明以下定理。你需要先陈述一个更一般的引理来得到一个有用的归纳假设，
    由它的话主定理就只是一个简单的推论了。 *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (short_circuit)  

    大部分现代编程语言对布尔 [and] 运算提供了“短路求值”的方法：要对
    [BAnd b1 b2] 进行求值，首先对 [b1] 求值。如果结果为 [false]，那么整个
    [BAnd] 表达式的求值就是 [false]，而无需对 [b2] 求值。否则，[b2]
    的求值结果就决定了 [BAnd] 表达式的值。

    请编写 [beval] 的另一种版本，它能以这种方式对 [BAnd] 执行短路求值，
    并证明它等价于 [beval]。（注：二者等价只是因为 Imp 的表达式求值相当简单。
    在更大的语言中该表达式可能会发散，此时短路求值的 [BAnd] _'并不'_
    等价于原始版本，因为它能让更多程序终止。） *)

(* 请在此处解答 

    [] *)

Module BreakImp.
(** **** 练习：4 星, advanced (break_imp)  

    像 C 和 Java 这样的指令式语言通常会包含 [break] 或类似地语句来中断循环的执行。
    在本练习中，我们考虑如何为 Imp 加上 [break]。首先，我们需要丰富语言的指令。 *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- 新增 *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** 接着，我们需要定义 [BREAK] 的行为。非形式化地说，只要 [BREAK]
    在指令序列中执行，它就会终止该序列的执行并发出最内层围绕它的循环应当终止的信号。
    （如果没有任何围绕它的循环，那么就终止整个程序。）最终状态应当与
    [BREAK] 语句执行后的状态相同。

    其要点之一在于当一个给定的 [BREAK] 位于多个循环中时应该做什么。
    此时，[BREAK] 应当只终止_'最内层'_的循环。因此，在执行完以下指令之后...

       X ::= 0;;
       Y ::= 1;;
       WHILE ~(0 = Y) DO
         WHILE true DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y - 1
       END

    ...[X] 的值应为 [1] 而非 [0]。

    表达这种行为的一种方式求值为求值关系添加一个形参，指定某个指令是否会执行
    [BREAK] 语句： *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, st' at next level).

(** 直觉上说，[st =[ c ]=> st' / s] 表示如果 [c] 在 [st] 状况下开始，
    它会在 [st'] 状态下终止，围绕它的最内层循环（或整个程序）
    要么收到立即退出的信号（[s = SBreak]），要么继续正常执行（[s = SContinue]）。

    “[st =[ c ]=> st' / s]”关系的定义非常类似于之前我们为一般求值关系
    （[st =[ c ]=> st']）给出的定义 -- 我们只需要恰当地处理终止信号。

    - 若指令为 [SKIP]，则状态不变，任何围绕它的循环继续正常执行。

    - 若指令为 [BREAK]，则状态保持不变但发出 [SBreak] 的信号。

    - 若指令为赋值，则根据状态更新该变量绑定的值，并发出继续正常执行的信号。

    - 若指令为 [TEST b THEN c1 ELSE c2 FI] 的形式，则按照 Imp 的原始语义更新状态，
      除此之外我们还要从被选择执行的分支中传播信号。

    - 若指令为一系列 [c1 ;; c2]，我们首先执行 [c1]。如果它产生了
      [SBreak]，我们就跳过 [c2] 的执行并将 [SBreak] 的信号传给其外围的上下文中;
      结果状态与执行 [c1] 后获得的相同。否则，我们在执行完 [c1] 后的状态下执行
      [c2] 并继续传递它产生的信号。

    - 最后，对于形如 [WHILE b DO c END] 的循环，其语义基本和此前相同。
      唯一的不同是，当 [b] 求值为 [true] 时执行 [c] 并检查它产生的信号。
      若信号为 [SContinue]，则按照原始语义继续执行。否则，我们终止此循环的执行，
      而其结果状态与当前迭代执行的结果相同。对于其它情况，由于 [BREAK]
      只终止最内层的循环，因此 [WHILE] 发出 [SContinue] 的信号。 *)

(** 基于以上描述，请完成 [ceval] 关系的定义。 *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  (* 请在此处解答 *)

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** 现在证明你定义的 [ceval] 的如下性质： *)

Theorem break_ignore : forall c st st' s,
     st =[ BREAK;; c ]=> st' / s ->
     st = st'.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem while_continue : forall b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s ->
  s = SContinue.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  st =[ WHILE b DO c END ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* 请在此处解答 *) Admitted.

(** [] *)
End BreakImp.

(** **** 练习：4 星, standard, optional (add_for_loop)  

    为该语言添加 C 风格的 [for] 循环指令，更新 [ceval] 的定义来定义
    [for] 循环，按需添加 [for] 循环的情况使得本文件中的所有证明都被
    Coq 所接受。

    [for] 循环的参数应当包含 (a) 一个初始化执行的语句；
    (b) 一个在循环的每次迭代中都执行的测试，它决定了循环是否应当继续；
    (c) 一个在循环的每次迭代最后执行的语句，以及 (d) 一个创建循环体的语句
    （你不必关心为 [for] 构造一个具体的记法，不过如果你喜欢，可以随意去做。） *)

(* 请在此处解答 

    [] *)


(* Fri Jul 19 00:33:13 UTC 2019 *)
