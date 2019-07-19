(** * Hoare: 霍尔逻辑（第一部分） *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Imp.

(** 在_'逻辑基础'_（_'软件基础'_ 的第一章) 中，
    我们用课程前面的部分中学习的数学工具研究了一个小型编程语言 Imp 。

    - 我们给 Imp 定义了_'抽象语法树（abstract syntax trees）'_；
      还有_'求值关系（evaluation relation）'_（一个在状态上的偏函数），
      它给出了程序的_'操作语义（operational semantics）'_。

      我们定义的这个小型语言实现了一些完善语言（例如 C、C++ 和 Java）
      的关键功能，包括基础的可变状态和控制流的概念。

    - 我们证明了许多_'元理论性质（metatheoretic properties）'_，也就是
      从高层次角度来说，这些性质是关于这整个语言的，而不是关于任何一段
      单独的程序。这包括了：

        - 求值过程的确定性

        - 用不同方式写下的定义之等价关系（例如，用求值函数和求值关系来定
          义算术表达式的化简规则）

        - 保证一系列程序必会停机

        - 数个实用的程序变换之正确性（从语义等价的角度来讲）

        - 程序的等价关系（在 [Equiv] 这一章里）。 *)

(** 如果在这里打住，我们已经有了一些实用的东西了：一套用来定义并讨论
    程序语言和它们的功能的工具。这些工具应用于程序语言的一些关键性质，
    （从数学角度来讲）是严谨和灵活的，并且是易于使用的。
    所有这些性质都是程序语言的设计者，编译器作者，以及用户所最关心的。
    当然，这些性质中的很多是极为基础的，以至于在我们对编程语言的认知
    中甚至不会把它们自然地当做“定理”来对待。但看似直观明显的属性有时候
    可能会非常微妙（有时也会错得很微妙！）。

    在这一卷稍后，我们将会在讨论_'类型（types）'_和_'类型可靠性
    （type soundness）'_时，回归到整个语言的元理论性质研究。不过现在
    我们要着眼于另外一些问题。

    我们的目标是给出一些_'软件形式化验证（program verification）'_
    的例子，也就是说，用 Imp 的精确定义来形式地证明某段程序符合某
    个规范。我们会建立一个叫做_'弗洛伊德-霍尔逻辑（Floyd-Hoare Logic）'_
    的系统（一般简称 _'霍尔逻辑（Hoare Logic）'_），它是 Imp 的语法构造
    加上了一个通用的“验证规则”的组合，可以用来说明包含这段结构的程序
    之正确性。

    霍尔逻辑发源于1960年代，至今为止依然是活跃的研究主题。
    它用于规范和验证许多学术界与工业界广泛使用的软件系统，并处于核心地位。

    霍尔逻辑组合了两个绝妙的想法：用自然的方式来编写程序的_'规范（specifications）'_
    ；和一种用来证明程序正确地实现了规范的_'复合证明技巧（compositional proof technique）'_
    ——其中“复合”的意思是，这些证明的结构直接反映了相应程序的结构。*)

(** 本章概览...
    主题：
      - 推理 Imp 程序_'功能正确性（functional correctness）'_ 的系统方法

    目标：
      - 一种自然表达_'程序规范（program specifications）'_的记号
      - 一种关于程序正确性的_'复合的（compositional）'_证明技巧

    计划：
      - 程序规范（断言／霍尔三元组）
      - 证明规则
      - 循环不变式
      - 带标注的程序
      - 例子 *)

(* ################################################################# *)
(** * 断言 *)

(** 要讨论程序的规范，我们需要的首先是一种在程序执行过程中某个时刻，
    关于程序性质做出_'断言（assertions）'_的方法。也就是说，我们要讨论执
    行到某处时，当时的内存状态。形式化地说，一项断言就是一系列关于 [state]
    的命题。*)

Definition Assertion := state -> Prop.

(** **** 练习：1 星, standard, optional (assertions)  

    用中文重新表述下列断言（或者用你最喜欢的语言）。 *)

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.
(* 请在此处解答 *)
End ExAssertions.
(** [] *)

(** 这种写下断言的方式可能过于繁琐，理由如下：
    (1) 我们写的每个断言都将以 [fun st => ] 开头；
    (2) 状态 [st] 是唯一我们希望用来再断言中查找变量的状态（我们将不会
    讨论在同一时间的两种不同状态。
    当我们非正式地讨论某些例子的时候，我们会简化一下：我们把开头的
    [fun st =>] 去掉，并且用 [X] 来代替 [st X] 所以，我们将把

      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)

    写成

      Z * Z <= m /\ ~((S Z) * (S Z) <= m).
*)

(** 这个例子也同时展示了我们将使用的另一种简便写法，我们将
    在关于霍尔逻辑的章节里都使用它：在非正式的断言中，大写字母例如 [X]、
    [Y]、[Z] 是 Imp 变量，而小写字母例如 [x]、[y]、[m]、[n] 则是一般的 Coq
    变量（类型是 [nat]）。这就是当我们把非正式断言翻译成正式断言时，把
    [X] 换成 [st X] 而留下 [m] 不变的理由。*)

(** 给出两断言 [P] 与 [Q]，我们说 [P] _'蕴含'_ [Q]，
    写作 [P ->> Q]，如果当 [P] 在 [st] 下成立，[Q] 也成立。*)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** 这里的记号 [hoare_spec_scope] 告诉 Coq， 这个记号不是全局的，
    我们打算把它用在特定的上下文里。[Open Scope] 告诉 Coq，这个文件就是
    一个我们将采用此记号的上下文。 *)

(** 我们也需要一个表达断言之间“当且仅当”的蕴含关系：*)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ################################################################# *)
(** * 霍尔三元组 *)

(** 接下来，我们需要一种描述命令行为的方式。*)

(** 广泛而言，一个命令的行为就是把一个状态转变成另一个状态，所以
    我们可以自然地通过命令运行前后的断言来描述一个命令。

      - “如果命令 [c] 在一个复合断言 [P] 的状态开始，并且如果 [c]
        最终在一个结束状态停机，这个结束状态会满足断言 [Q]。”

    这样的描述叫做_'霍尔三元组（Hoare Triple）'_。断言 [P] 叫做 [c]
    的_'前置条件（precondition）'_，而 [Q] 叫做 _'后置条件（postcondition）'_。*)

(** 形式化地： *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

(** 因为我们将会在霍尔三元组上做很多研究，所以一个紧凑的记号是非常便
    利的：

       {{P}} c {{Q}}.

    （传统的记号是 [{P} c {Q}]，不过单花括号已经被用在 Coq 中其
    它东西上了。*)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** **** 练习：1 星, standard, optional (triples)  

    用中文重新表述下列霍尔三元组。

   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}}
      c
      {{Y = real_fact m}}

   6) {{X = m}}
      c
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
*)
(* 请在此处解答 

    [] *)

(** **** 练习：1 星, standard, optional (valid_triples)  

    下列的霍尔三元组是否_'有效'_，亦即，表述的 [P]、[c]、[Q] 之间的
    关系是否为真？

   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5;; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE true DO SKIP END {{False}}

   8) {{X = 0}}
        WHILE X = 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
        WHILE ~(X = 0) DO X ::= X + 1 END
      {{X = 100}}
*)
(* 请在此处解答 

    [] *)

(** 为了热身，这里有两个关于霍尔三元组的简单定理。
    （确保你弄懂它们的意思。）*)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ################################################################# *)
(** * 证明规则 *)

(** 霍尔逻辑的目标是提供一种_组合的_ 方法，
    用来证明特定三元组的正确性。
    也即，我们希望一段程序的正确性证明的结构反映程序本身。
    为了达成这个目的，在下面的小节中，我们为不同语法形式的 Imp
    命令引入不同的推理规则：关于赋值的、关于顺序执行的、
    关于条件执行的等等。还有一些“结构的”规则用来组合它们。
    然后我们将能证明一段程序是正确的，使用这些证明规则，甚至不用展开
    [hoare_triple] 的定义。 *)

(* ================================================================= *)
(** ** 赋值 *)

(** 赋值是霍尔逻辑的规则中最基础的一个。下述是它的工作方式。

    考虑这个有效的霍尔三元组：

       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}

    用中文讲：如果我们从一个 [Y] 是 [1] 的状态开始，
    然后我们把 [Y] 赋给 [X]，我们最终会得到一个 [X] 是 [1] 的状态。
    也即，“等于 [1]”这个属性被从 [Y] 传递给了 [X]。 *)

(** 相似地，在

       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}

    里，同样的属性（等于 [1]）被从赋值命令的右侧 [Y + Z] 传递给了 [X]。*)

(** 更一般地, 如果 [a] 是_'任意'_算术表达式，那么

       {{ a = 1 }}  X ::= a  {{ X = 1 }}

    是一个有效的霍尔三元组。 *)

(** 甚至更一般地，为了得到 [Q] 在 [X ::= a] 后仍然成立，我们需要先有
    [Q] 在 [X ::= a] 前成立，不过_'所有在 [Q] 中出现的'_ [X] 被
    替换为 [a]。这给出了霍尔逻辑中赋值的规则

      {{ Q [X |-> a] }} X ::= a {{ Q }}

    其中 "[Q [X |-> a]]" 读作 “在 [Q] 中把 [X] 换成 [a]”。 *)

(** 例如，下列这些是赋值规则正确的应用：

      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}
      X ::= X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3 }}
      X ::= 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5) }}
      X ::= 3
      {{ 0 <= X /\ X <= 5 }}
*)

(** 为了形式化这个规则，我们必须先把“在一个断言中将 Imp 变量替换为一个
    表达式” 的概念形式化，我们把这叫做“断言替换”，或者是 [assn_sub]。
    也就是说，给出命题 [P]、变量 [X]、算术表达式 [a]，我们想要生成一个
    新的命题 [P']，它和 [P] 一样，不过 [P'] 应该用 [a] 来取代所有
    [P] 提及 [X] 之处。*)

(** 因为 [P] 是一个任意的 Coq 断言，我们不能直接“编辑”它的文本部分。不
    过，我们可以通过将 [P] 在下述新的状态中计算来达到相同的效果：*)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

(** 也就是说，[P [X |-> a]] 是一个新的断言——我们把它叫做 [P'] ——
    它就是 [P]，不过当 [P] 在当前状态中查找变量 [X] 的时候，[P'] 使用表
    达式 [a] 的值。*)

(** 为了演示工作原理，我们来计算一下这几个例子中发生了些什么。首先，假设
    [P'] 是 [(X <= 5) [X |-> 3]] ——或者，更形式化地， [P'] 是 Coq 表达式

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),

    它简化为

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)

    并且可以进一步简化为

    fun st =>
      ((X !-> 3 ; st) X) <= 5

   最终是

    fun st =>
      3 <= 5.

    也就是说，[P'] 是一个断言指出 [3] 小于等于 [5]（像我们想的一样）。*)

(** 一个更有趣的例子是，假设 [P'] 是 [(X <= 5) [X |-> X + 1]]。形式化地，[P']
    是 Coq 表达式

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    它简化为

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    并且进一步简化为

    fun st =>
      (aeval st (X + 1)) <= 5.

    也就是说，[P'] 指出 [X + 1] 最多是 [5]。
*)

(** 现在，利用替换的概念，我们可以给出下述赋值证明规则的严谨证明：

      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)

(** 我们可以形式化地证明这个规则是正确的。*)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(** 下述是一个利用这个规则的形式化证明。*)

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X + 1]}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  (* 课上已完成 *)
  apply hoare_asgn.  Qed.

(** 当然，更加有帮助的是证明这个更简单的三元组：

      {{X < 4}} X ::= X + 1 {{X < 5}}

    我们会在下一节中了解怎么做。*)

(** **** 练习：2 星, standard (hoare_asgn_examples)  

    将下列非正式的霍尔三元组……

    1) {{ (X <= 10) [X |-> 2 * X] }}
       X ::= 2 * X
       {{ X <= 10 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}

   ……翻译成正式的表达（名字叫 [assn_sub_ex1] 和 [assn_sub_ex2]）
   并且用 [hoare_asgn] 来证明它们。*)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_hoare_asgn_examples : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard, recommended (hoare_asgn_wrong)  

    几乎所有人在看赋值规则第一眼就会觉得它是反向的。如果你还感觉很
    迷惑，思考一些“正向”的规则可能有帮助。这里是一个看起来挺自然的
    霍尔三元组：

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}

    请给出一个能说明这个规则是错误的反例，并非形式化地说明它确实
    是个反例。（提示： 这个规则量化的是所有的算术表达式 [a]，你的
    反例应该包含一个使这个规则不能正确工作的 [a]。）*)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_hoare_asgn_wrong : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, advanced (hoare_asgn_fwd)  

    然而，通过引入一个_'参数'_ [m]（一个 Coq 整数）来记录 [X] 原
    来的值，我们可以定义一个赋值的证明规则，它可以，直觉上讲，“正向地
    工作”。

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X ::= a
       {{fun st => P st' /\ st X = aeval st' a }}
       (其中 st' = (X !-> m ; st))

    可以注意到，在赋值发生之前我们用 [X] 原来的值重新构造了状态
    [st']。证明这个规则是正确的。（注意，这个规则比 [hoare_asgn] 复杂些。)
*)

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, advanced, optional (hoare_asgn_fwd_exists)  

    另外一种定义正向赋值规则的方式是，对变量在赋值之前的值做存在量化。
    证明这是正确的。

      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X ::= a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
*)

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
  intros a P.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 缩放 *)

(** 有的时候我们从其它证明规则中得到的前置条件和后置条件可能并不
    是我们想使用的那个情形：它们可能在逻辑上符合需要，但是有着不同的
    形式而无法和期望的情形匹配；或者我们所得到的这个三元组的前条件
    太弱，抑或是后条件太强。

    例如，

      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}}

    可以直接由赋值规则所得，而

      {{True}} X ::= 3 {{X = 3}}

    却不行。这个三元组是有效的，不过它并不是 [hoare_asgn] 的实例，因
    为 [True] and [(X = 3) [X |-> 3]] 在语法上并不是相同的断言。然而，
    它们在逻辑上_'等价'_，所以前面那个三元组成立，后者也一定成立。
    我们把这种想法用下列规则写出来：

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)

(** 仔细考虑一下这个想法，我们可以看到对一个有效的三元组加强前置条件
    或者减弱后置条件总是能得到一个有效的三元组。这种想法可以用两条
    _'缩放规则（Rules of Consequence）'_ 来描述：

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** 下列是形式化的版本： *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

(** 例如，我们可以这样应用第一条规则：

      {{ True }} ->>
      {{ 1 = 1 }}
    X ::= 1
      {{ X = 1 }}

    或者，形式化地：*)

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  (* 课上已完成 *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.

(** 我们也可以用它来证明之前提到的例子。

      {{ X < 4 }} ->>
      {{ (X < 5)[X |-> X + 1] }}
    X ::= X + 1
      {{ X < 5 }}

   或者，形式化地：*)

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  (* 课上已完成 *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X < 5) [X |-> X + 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. omega.
Qed.

(** 最后，为了证明中的方便，我们有一个组合起来的缩放规则，可以让
    我们同时改变前置条件和后置条件。

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(** ** 题外话：[eapply] 策略*)

(** 这又是一个来看一下 [eapply] 策略的好机会。我们在逻辑基础的
    [Auto] 一章中已经简略介绍过了。

    在 [hoare_asgn_example1] 和 [hoare_consequence] 中，我们必
    须要显式地写出 “[with (P' := ...)]” 来保证 [hoare_consequence]
    中假定的所有元变量都被设为了一个具体的值。（这是因为 [P']
    没有在 [hoare_consequence_pre] 的结论中出现，将结论匹配于
    当前的目标并不能把 [P'] 约束到一个具体的断言上。）

    这很烦人，既因为这个断言有点长，而且，在 [hoare_asgn_example1] 中，
    我们紧接着的下一步——应用 [hoare_asgn] 规则——将会直接给出
    这个断言应该是什么！这时，我们可以用 [eapply] 代替 [apply]
    来告诉 Coq，大概是“耐心点儿：空缺的那部分会在证明中过会儿
    再填上。” *)

Example hoare_asgn_example1' :
  {{fun st => True}}
  X ::= 1
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** 一般来说，[eapply H] 策略和 [apply H] 的工作方式相同，不过
    当匹配目标和 [H] 的结论时，若无法确定如何实例化 [H] 的前提中出
    现的变量，[eapply H] 并不会失败，而是会把这些变量
    替换为_'存在变量（existential variables）'_（写做 [?nnn]）,
    它的功能是作为接下来证明中会确定（通过进一步的合一）
    的变量的占位符。*)

(** 如果要 [Qed] 成功，所有的存在变量都要在证明结束前被确定。
    否则 Coq 将会（正义地）拒绝接受这个证明。回想，Coq 策略
    将构建证明对象，证明对象中还有一些存在变量没有被确定。*)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.

(** Coq 在 [apply HP] 之后提出了一个警告。（“All the remaining goals
    are on the shelf”，意思是我们已经完成了所有的顶层的证明目标，
    然而在这个过程中我们将一些放到一边打算待会做，我们还没有完成它们。）
    用 [Qed] 结束证明会产生一个错误。*)
Abort.

(** 一个附加的限制是，若项中含有在创建存在变量时还不存在的普通变量，则存在变量无法被实例化。
   （原因当然是如果我们允许这样做逻辑系统就会变得不再自洽。） *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].

(** 在这里使用 [apply HP'] 将会失败并产生如下错误：

      Error: Impossible to unify "?175" with "y".

    有一个简单的解决办法：把 [destruct HP] 提到 [eapply HQ] _'之前'_。 *)
Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** 最后一步中的 [apply HP'] 将目标中的存在变量匹配于变量 [y]。

    注意，[assumption] 策略并不能在这里正常工作，因为它不能处理
    存在变量。然而，Coq 也提供了一个 [eassumption] 策略，如果当
    前有一个前提通过将结论中的存在变量填好而匹配，它就解决目标。
    我们可以用它来代替 [apply HP']，如果你想的话。 *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** **** 练习：2 星, standard (hoare_asgn_examples_2)  

    将下述的非形式化霍尔三元组

       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

   翻译成正式的表达（把它们叫做 [assn_sub_ex1'] 和 [assn_sub_ex2']）
   并且使用 [hoare_asgn] 和 [hoare_consequence_pre] 证明它们。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_hoare_asgn_examples_2 : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 跳过 *)

(** 因为 [SKIP] 并不改变当前状态，它会保持 [P]：

      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ================================================================= *)
(** ** 顺序 *)

(** 更加有趣的是，如果命令 [c1] 将一个 [P] 成立的状态转变为 [Q]
    成立的状态，而如果 [c2] 将 [Q] 成立的状态转变为 [R] 成立的，
    那么先执行 [c1] 然后执行 [c2] 将会把一个 [P] 成立的状态转变
    为一个 [R] 成立的状态：

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** 可以注意到在 [hoare_seq] 中，前提以一个相反的顺序给出
    （先 [c2] 再 [c1]）。这符合在大部分情况中自然的信息输入顺序，
    因为最自然的构造一个霍尔逻辑证明的方式是从这个程序的末尾开始
    （在后置条件的状态中），然后逆推直到程序开始的地方。 *)

(** 一种非形式化地展示利用组合规则的证明的方式是将其写为“带标注
    的程序”，其中中间状态断言 [Q] 写在 [c1] 和 [c2] 之间：

      {{ a = n }}
    X ::= a;;
      {{ X = n }}    <--- decoration for Q
    SKIP
      {{ X = n }}
*)

(** 下面是一个同时包括赋值和组合的例子。 *)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* 组合右侧 *)
    apply hoare_skip.
  - (* 组合左侧 *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

(** 我们一般会将 [hoare_seq] 和
    [hoare_consequence_pre] 以及 [eapply] 策略一起使用，如上所示。*)

(** **** 练习：2 星, standard, recommended (hoare_asgn_example4)  

    将这个“标注程序”翻译成正式证明：

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}

   （带 “[->>]” 的标记代表了使用 [hoare_consequence_pre]。） *)

Example hoare_asgn_example4 :
  {{fun st => True}}
  X ::= 1;; Y ::= 2
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (swap_exercise)  

    写一个 Imp 程序 [c]，用来交换变量 [X] 和 [Y] 并且说明
    它符合如下规范：

      {{X <= Y}} c {{Y <= X}}

     你的证明不应该使用 [unfold hoare_triple]。
     （提示：记住赋值规则在“从后往前”，即从后置条件到前置条件应用时工作得最好。
     因此你的证明可以从程序的后面开始逐步往前进行。） *)

Definition swap_program : com
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (hoarestate1)  

    解释为何下列命题无法被证明：

      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
           X ::= 3;; Y ::= a
         {{fun st => st Y = n}}.
*)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_hoarestate1 : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 条件 *)

(** 我们需要什么样的规则来推理条件命令呢？

    当然，如果断言 [Q] 在两个分支执行后都成立，它就对整个条件命令成立。
    所以我们可以试着给出：

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} TEST b THEN c1 ELSE c2 {{Q}}
*)

(** 然而，这个规则太弱了。例如，用这个规则我们并不能推理出

     {{ True }}
     TEST X = 0
       THEN Y ::= 2
       ELSE Y ::= X + 1
     FI
     {{ X <= Y }}

   因为这个规则并没有告诉我们在“THEN”和“ELSE”分支中赋值时的状态。*)

(** 不过我们还是可以表述得更精确。在“THEN”分支中，[b] 化简为
    [true]，而在“ELSE”分支中我们知道它化简为 [false]。
    我们可以让这个信息作为 [c1] 和 [c2] 的假设出现可以让我们分别研究
    [c1] 和 [c2] 的行为（亦即它们为什么能导出后置条件 [Q]）。

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}
*)

(** 要形式化地解释这个规则，我们还需要做一点微小的工作。
    严格来说，我们写下的断言 [P /\ b]，是一个断言和一个布尔表达式的
    合取——也就是说，它并不能通过类型检查。为了让它正常工作，
    我们必须要把 [b] “升格” 为一个断言。我们用 [bassn b] 来表示“
    [b] 在给定的状态中化简到 [true]”。*)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** 下列是一些有关于 [bassn] 的有用的引理：*)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** 现在我们就可以形式化条件命令的证明规则，并且证明它的正确性。*)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b 是 true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b 是 false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

(* ----------------------------------------------------------------- *)
(** *** 例子 *)

(** 下面是刚刚例子的形式化证明，我们用规则来证明程序符合规范。*)

Example if_example :
    {{fun st => True}}
  TEST X = 0
    THEN Y ::= 2
    ELSE Y ::= X + 1
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* 课上已完成 *)
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply eqb_eq in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** **** 练习：2 星, standard (if_minus_plus)  

    用 [hoare_if] 证明下面的三元组。不要使用 [unfold hoare_triple]。*)

Theorem if_minus_plus :
  {{fun st => True}}
  TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 练习：单侧条件 *)

(** **** 练习：4 星, standard (if1_hoare)  

    在这个练习中我们考虑对 Imp 加入形如 [IF1 b THEN c FI] 的“单边条件”。
    这里 [b] 是个布尔表达式而 [c] 是一个命令。如果 [b] 化简为 [true]， [c]
    就被执行，而如果 [b] 化简为 [false]， [IF1 b THEN c FI] 就啥也不做。

    我们推荐你，在尝试之后的联系之前，先完成这个。因为它应该会让你对材料
    有更加完善的认知。*)

(** 第一步是引入之前出现的命令和记号，并且加入新的命令。（我们已经
    帮你弄好了。在这里用一个分离的模组来避免污染全局命名空间。）*)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity) : imp_scope.

(** 接下来我们需要拓展求值规则以包含 [IF1] 的情形。我们把任务交给你……
    应该网 [ceval] 中加入哪条（那些）命令来化简单边分支命令？*)

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

  where "st '=[' c ']=>' st'" := (ceval c st st').
Close Scope imp_scope.

(** 现在我们把霍尔三元组的定义和记号重新写在这里。*)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

(** 最终你得证明一个定理 [hoare_if1]，指出一个关于单边条件语句的证明规则。
    你得试着尽可能让它既正确又精准。*)

(* 请在此处解答 *)

(** 要拿到全部的分数，你还得证明一个定理 [hoare_if1_good] 指出你的规则足够精细，
    能够证明下列的霍尔三元组是有效的：

  {{ X + Y = Z }}
  IF1 ~(Y = 0) THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: 提示，你的证明会用到其它证明规则。因为我们开了个新模组，你得把你用到
    的那些都拷到这来。*)

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  (IF1 ~(Y = 0) THEN
    X ::= X + Y
  FI)%imp
  {{ fun st => st X = st Z }}.
Proof. (* 请在此处解答 *) Admitted.

End If1.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_if1_hoare : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 循环 *)

(** 最后，我们需要一个用来推理循环的规则。 *)

(** 假设我们有一个循环

      WHILE b DO c END

    我们希望找到一个前置条件 [P] 和一个后置条件 [Q] 满足使

      {{P}} WHILE b DO c END {{Q}}

    成为一个有效的霍尔三元组。 *)

(** 首先，让我们考虑 [b] 在开始的时候是 [false] 的情况，
    也就是说，让我们假设这个循环的循环体根本不执行。在这种情形
    下，这个循环的行为类似于 [SKIP]，所以我们可能可以试着先这样
    写：*)

(**

      {{P}} WHILE b DO c END {{P}}.
*)

(** 不过就像我们在上面对条件语句分析时那样，我们还会有一点附加
    的信息：除了 [P] 成立以外，[b] 会在执行完毕以后化简为 [false]。
    所以，我们可以再添补一下后置条件： 

      {{P}} WHILE b DO c END {{P /\ ~ b}}
*)

(** 那么循环体被执行的情形呢？为了确保 [P] 在循环最终退出
    的时候成立，我们当然需要保证命令 [c] 执行后 [P] 成立。
    进一步说，因为 [P] 在 [c] 第一次执行前成立，每次 [c] 执行完成
    都会重新满足作为后置条件的 [P]，我们可以假设 [P] 在 [c] 执行前
    就成立。总结为以下规则：

                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~ b}}

    这几乎就是我们想要的规则，不过它还有一点可以改进的地方：在循环体
    开始是的时候，我们不止知道 [P] 成立，还有条件 [b] 会在当前状态
    中化简为 [true]。*)

(** 这给我们带来了一点额外的信息用来推论 [c] （用来说明它结束时
    满足不变式）。

    而这会将我们导向此规则的最终版本：

               {{P /\ b}} c {{P}}
        ----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}

    断言 [P] 叫做_'循环不变式（invariant of the loop）'_。
*)

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* 像之前见到过的，我们需要对 [He] 做归纳来推理。
     因为，在“继续循环”的情形中，假设会是关于整个循环而不只是关于 [c] 的。*)
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(** 令人费解的事情是，我们把断言 [P] 叫做“循环不变式” 并不代表它只是由
    （上述问题中的）循环体所保证（也就是 [{{P}} c {{P}}]，其中 [c] 是循环体），
    而实际上 [P] _'加上循环条件为真'_才是 [c] 能够推出后置条件所
    需要的前置条件。

    这是略微弱化的（但十分重要）前提。例如，如果 [P] 是断言 [X = 0]，那么
    [P] _'是'_下述循环的不变式：

      WHILE X = 2 DO X := 1 END

    即使它很明显_'不是'_只由循环体所导出。*)

Example while_example :
    {{fun st => st X <= 3}}
  WHILE X <= 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.
(** 我们可以使用 WHILE 规则来证明下列的霍尔三元组。 *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  (* 课上已完成 *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* 循环体维持不变式 *)
    apply hoare_post_true. intros st. apply I.
  - (* 循环体和循环条件不成立可以导出后条件 *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* 前条件可以导出不变式 *)
    intros st H. constructor.  Qed.

(** 这很显然，因为我们知道 [hoare_triple] 的定义断言了仅当
    该命令停机时其后条件才成立。如果命令不停机，我们可以在后置条件中证明任何我们需要的
    东西。*)

(** 我们一般把那些只讨论当命令最终停机（而不证明它们确实停机）的
    证明规则叫做描述“部分（partial）”正确性的逻辑。我们也可以给出描述“完全（total）”
    正确性（也就是带有命令停机的假设）的证明规则。不过在这章里我们只介绍部分正确性。*)

(* ----------------------------------------------------------------- *)
(** *** 练习：[REPEAT] *)

(** **** 练习：4 星, advanced (hoare_repeat)  

    在这个练习中，我们会往 Imp 里面加一种新的命令：[REPEAT] c [UNTIL] b [END]。
    请你写出 [REPEAT] 的求值规则，并且写一个关于它的霍尔逻辑证明规则。
    （回想在 [Auto] 中给出的规则，试着自己把这个写出来，别偷看。）*)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] 的行为类似于 [WHILE]，除了它的循环条件是在循环体结束
    _'后'_检查的，并且只要循环条件是 [false] 循环就会被执行。因为
    这样，循环体至少会被执行一次。*)

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

(** 在下面为 [ceval] 加入 [REPEAT]。你可以把 [WHILE] 的规则当作一个
    模板，不过注意 [REPEAT] 的循环体至少要执行一次，并且循环会在条件
    为真的时候结束。*)

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : state -> com -> state -> Prop :=
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

where "st '=[' c ']=>' st'" := (ceval st c st').

(** 下面是一些之前出现的定义，我们把它重新写一遍它就会用新的 [ceval]。 *)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** 为了保证写出了正确的 [REPEAT] 计算规则，请你证明 [ex1_repeat]
    能够正常计算。*)

Definition ex1_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL X = 1 END.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  (* 请在此处解答 *) Admitted.

(** 现在写出并证明一个定理 [hoare_repeat] 表达一个 [repeat]
    命令的合理证明规则。你可以把 [hoare_while] 当作一个模型，
    试着让你的规则尽可能地精确。 *)

(* 请在此处解答 *)

(** 要拿到全部的分数，请确保（非正式即可）你的规则可以用来证明以下
    的霍尔三元组成立。

  {{ X > 0 }}
  REPEAT
    Y ::= X;;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)

End RepeatExercise.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_hoare_repeat : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * 总结 *)

(** 到此为止，我们引入了用来推理 Imp 程序的工具，霍尔逻辑。霍尔逻辑
    的证明规则有：

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}

    下一章中我们会看如何用这些规则证明程序满足它们行为的规范。 *)

(* ################################################################# *)
(** * 附加练习 *)

(** **** 练习：3 星, standard (hoare_havoc)  

    在这个练习中我们将会为一种 [HAVOC] 命令实现证明规则，这个命令类似于
    [Imp] 中的 [any] 表达式。

    首先我们把这些命令放在一个分离的模块里，并且把命令的语法和粗略语义
    写下来。*)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

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
  | E_Havoc : forall st X n,
      st =[ HAVOC X ]=> (X !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

(** 对霍尔三元组的定义和之前完全一致。 *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

(** 请通过定义 [havoc_pre] 来创建一个关于 [HAVOC] 的证明规则，并
    证明此规则是正确的。*)

Definition havoc_pre (X : string) (Q : Assertion) : Assertion
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* 请在此处解答 *) Admitted.

End Himp.
(** [] *)

(** **** 练习：4 星, standard, optional (assert_vs_assume)  *)

Module HoareAssertAssume.

(**  在这个练习中我们会对 Imp 加入语句 [ASSERT] 和 [ASSUME]。这两个命令
     都是用来指出某个布尔表达式应该在任何一次程序运行到这里的时候都为真。
     但是它们有下列区别：

    - 如果 [ASSERT] 失败了，程序就会进入错误状态并且退出。

    - 如果 [ASSUME] 失败了，程序就不能运行。换句话说这段程序会卡住，没有
      最终状态。

    新的一系列命令是：*)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

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
Notation "'ASSERT' b" :=
  (CAssert b) (at level 60).
Notation "'ASSUME' b" :=
  (CAssume b) (at level 60).

(** 要定义 [ASSERT] 和 [ASSUME] 的行为，我们必须要加入一个表示错误
    状态的记号，它指出某个 [ASSERT] 失败了。我们修改一下 [ceval]
    规则，让它是开始状态和“结束状态或者是 [error]”的关系。[result]
    类型是程序结束时的值，要么是 [state] 要么是 [error]。*)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** 现在我们可以给出新语言的 [ceval] 了。*)

Inductive ceval : com -> state -> result -> Prop :=
  (* 稍加修改的旧有规则 *)
  | E_Skip : forall st,
      st =[ SKIP ]=> RNormal st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ;; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ;; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ WHILE b DO c END ]=> r ->
      st  =[ WHILE b DO c END ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ WHILE b DO c END ]=> RError
  (* Assert 和 Assume 的规则 *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ ASSERT b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ ASSERT b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ ASSUME b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** 我们重新定义霍尔三元组：现在，[{{P}} c {{Q}}] 的意思是，
    当 [c] 在一个满足 [P] 的状态中启动并且停机在一个状态 [r]，那么 [r]
    不是错误并且满足 [Q]。*)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** 为了测试你对这个修改的理解是否正确，请给出一组前置条件和后置条件，
    它们可以被 [ASSUME] 语句导出却不能被 [ASSERT] 导出。然后证明任何关于
    [ASSERT] 的三元组换成 [ASSUME] 也是正确的。*)

Theorem assert_assume_differ : exists P b Q,
       ({{P}} ASSUME b {{Q}})
  /\ ~ ({{P}} ASSERT b {{Q}}).
Proof.
(* 请在此处解答 *) Admitted.

Theorem assert_implies_assume : forall P b Q,
     ({{P}} ASSERT b {{Q}})
  -> ({{P}} ASSUME b {{Q}}).
Proof.
(* 请在此处解答 *) Admitted.

(** 你的任务是为 [ASSERT] 和 [ASSUME] 创建霍尔规则，并且用它们证明
    一个小程序是正确的。把你的规则起名为 [hoare_assert] 和 [hoare_assume]。

    为了你方便点，我们把新语义上的那些旧有的霍尔规则帮你证明好了。*)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ']].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ]].
        inversion Heq; subst. assumption.
  - (* 找到矛盾的假设 *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _]].
     inversion C.
Qed.

(**  把你的霍尔规则，[hoare_assert] 和 [hoare_assume] 写在下面。*)

(* 请在此处解答 *)

(** 下列是其它证明规则（用来检查是否合理）*)
Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b 是 true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b 是 false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1]].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _]]. inversion C.
     + split; assumption.
Qed.

Example assert_assume_example:
  {{fun st => True}}
  ASSUME (X = 1);;
  X ::= X + 1;;
  ASSERT (X = 2)
  {{fun st => True}}.
Proof.
(* 请在此处解答 *) Admitted.

End HoareAssertAssume.
(** [] *)

(* Fri Jul 19 00:33:14 UTC 2019 *)
