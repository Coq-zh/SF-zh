(** * Induction: 归纳证明 *)

(** 在开始之前，我们需要把上一章中所有的定义都导入进来： *)

From LF Require Export Basics.

(** For the [Require Export] to work, Coq needs to be able to
    find a compiled version of [Basics.v], called [Basics.vo], in a directory
    associated with the prefix [LF].  This file is analogous to the [.class]
    files compiled from [.java] source files and the [.o] files compiled from
    [.c] files.

    First create a file named [_CoqProject] containing the following line
    (if you obtained the whole volume "Logical Foundations" as a single
    archive, a [_CoqProject] should already exist and you can skip this step):

      [-Q . LF]

    This maps the current directory ("[.]", which contains [Basics.v],
    [Induction.v], etc.) to the prefix (or "logical directory") "[LF]".
    PG and CoqIDE read [_CoqProject] automatically, so they know to where to
    look for the file [Basics.vo] corresponding to the library [LF.Basics].

    Once [_CoqProject] is thus created, there are various ways to build
    [Basics.vo]:

     - In Proof General: The compilation can be made to happen automatically
       when you submit the [Require] line above to PG, by setting the emacs
       variable [coq-compile-before-require] to [t].

     - In CoqIDE: Open [Basics.v]; then, in the "Compile" menu, click
       on "Compile Buffer".

     - From the command line: Generate a [Makefile] using the [coq_makefile]
       utility, that comes installed with Coq (if you obtained the whole
       volume as a single archive, a [Makefile] should already exist
       and you can skip this step):

         [coq_makefile -f _CoqProject *.v -o Makefile]

       Note: You should rerun that command whenever you add or remove Coq files
       to the directory.

       Then you can compile [Basics.v] by running [make] with the corresponding
       [.vo] file as a target:

         [make Basics.vo]

       All files in the directory can be compiled by giving no arguments:

         [make]

       Under the hood, [make] uses the Coq compiler, [coqc].  You can also
       run [coqc] directly:

         [coqc -Q . LF Basics.v]

       But [make] also calculates dependencies between source files to compile
       them in the right order, so [make] should generally be prefered over
       explicit [coqc].

    如果你遇到了问题（例如，稍后你可能会在本文件中遇到缺少标识符的提示），
    那可能是因为没有正确设置 Coq 的“加载路径”。指令 [Print LoadPath.]
    能帮你理清这类问题。

    特别是，如果你看到了像这样的信息：

        [Compiled library Foo makes inconsistent assumptions over
        library Bar]

    check whether you have multiple installations of Coq on your machine.
    It may be that commands (like [coqc]) that you execute in a terminal
    window are getting a different version of Coq than commands executed by
    Proof General or CoqIDE.

    - Another common reason is that the library [Bar] was modified and
      recompiled without also recompiling [Foo] which depends on it.  Recompile
      [Foo], or everything if too many files are affected.  (Using the third
      solution above: [make clean; make].)

    再给 CoqIDE 用户一点技巧：如果你看到了 [Error: Unable to locate
    library Basics]，那么可能的原因是用 _'CoqIDE'_ 编译的代码和在指令行用
    _'coqc'_ 编译的不一致。这通常在系统中安装了两个不兼容的 [coqc] 时发生
    （一个与 CoqIDE 关联，另一个与指令行的 [coqc] 关联）。这种情况的变通方法
    就是只使用 CoqIDE 来编译（即从菜单中选择“make”）并完全避免使用 [coqc]。 *)

(* ################################################################# *)
(** * 归纳法证明 *)

(** 我们在上一章中通过基于化简的简单论据证明了 [0] 是 [+] 的左幺元。
    我们也观察到，当我们打算证明 [0] 也是 [+] 的 _'右'_ 幺元时... *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

(** ...事情就没这么简单了。只应用 [reflexivity] 的话不起作用，因为 [n + 0]
    中的 [n] 是任意未知数，所以在 [+] 的定义中 [match] 匹配无法被化简。 *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** 即便用 [destruct n] 分类讨论也不会有所改善：诚然，我们能够轻易地证明 [n = 0]
    时的情况；但在证明对于某些 [n'] 而言 [n = S n'] 时，我们又会遇到和此前相同的问题。 *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* 虽然目前还没啥问题... *)
  - (* n = S n' *)
    simpl.       (* ...不过我们又卡在这儿了 *)
Abort.

(** 虽然还可以用 [destruct n'] 再推进一步，但由于 [n] 可以任意大，
    如果照这个思路继续证明的话，我们永远也证不完。 *)

(** 为了证明这种关于数字、列表等归纳定义的集合的有趣事实，
    我们通常需要一个更强大的推理原理：_'归纳'_。

    回想一下 _'自然数的归纳法则'_，你也许曾在高中的数学课上，在某门离散数学课上或
    在其它类似的课上学到过它：若 [P(n)] 为关于自然数的命题，而当我们想要证明 [P]
    对于所有自然数 [n] 都成立时，可以这样推理：
         - 证明 [P(O)] 成立；
         - 证明对于任何 [n']，若 [P(n')] 成立，那么 [P(S n')] 也成立。
         - 最后得出 [P(n)] 对于所有 [n] 都成立的结论。

    在 Coq 中的步骤也一样：我们以证明 [P(n)] 对于所有 [n] 都成立的目标开始，
    然后（通过应用 [induction] 策略）把它分为两个子目标：一个是我们必须证明
    [P(O)] 成立，另一个是我们必须证明 [P(n') -> P(S n')]。下面就是对该定理的用法： *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(** 和 [destruct] 一样，[induction] 策略也能通过 [as...] 从句为引入到
    子目标中的变量指定名字。由于这次有两个子目标，因此 [as...] 有两部分，用 [|]
    隔开。（严格来说，我们可以忽略 [as...] 从句，Coq 会为它们选择名字。
    然而在实践中这样不好，因为让 Coq 自行选择名字的话更容易导致理解上的困难。）

    在第一个子目标中 [n] 被 [0] 所取代。由于没有新的变量会被引入，因此 [as ...]
    字句的第一部分为空；而当前的目标会变成 [0 + 0 = 0]：使用化简就能得到此结论。

    在第二个子目标中，[n] 被 [S n'] 所取代，而对 [n'] 的归纳假设（Inductive
    Hypothesis），即 [n' + 0 = n'] 则以 [IHn'] 为名被添加到了上下文中。
    这两个名字在 [as...] 从句的第二部分中指定。在此上下文中，待证目标变成了
    [(S n') + 0 = S n']；它可被化简为 [S (n' + 0) = S n']，而此结论可通过
    [IHn'] 得出。 *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* 课上已完成 *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** （其实在这些证明中我们并不需要 [intros]：当 [induction]
    策略被应用到包含量化变量的目标中时，它会自动将需要的变量移到上下文中。） *)

(** **** 练习：2 星, standard, recommended (basic_induction)  

    用归纳法证明以下命题。你可能需要之前的证明结果。 *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* 请在此处解答 *) Admitted.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (double_plus)  

    考虑以下函数，它将其参数乘以二： *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** 用归纳法证明以下关于 [double] 的简单事实： *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (evenb_S)  

    我们的 [evenb n] 定义对 [n - 2] 的递归调用不大方便。这让证明 [evenb n]
    时更难对 [n] 进行归纳，因此我们需要一个关于 [n - 2] 的归纳假设。
    以下引理赋予了 [evenb (S n)] 另一个特征，使其在归纳时能够更好地工作： *)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (destruct_induction)  

    请简要说明一下 [destruct] 策略和 [induction] 策略之间的区别。

(* 请在此处解答 *)
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_destruct_induction : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * 证明里的证明 *)

(** 和在非形式化的数学中一样，在 Coq 中，大的证明通常会被分为一系列定理，
    后面的定理引用之前的定理。但有时一个证明会需要一些繁杂琐碎的事实，
    而这些事实缺乏普遍性，以至于我们甚至都不应该给它们单独取顶级的名字。
    此时，如果能仅在需要时简单地陈述并立即证明所需的“子定理”就会很方便。
    我们可以用 [assert] 策略来做到。例如，我们之前对 [mult_0_plus]
    定理的证明引用了前一个名为 [plus_O_n] 的定理，而我们只需内联使用 [assert]
    就能陈述并证明 [plus_O_n]： *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** [assert] 策略引入两个子目标。第一个为断言本身，通过给它加前缀 [H:]
    我们将该断言命名为 [H]。（当然也可以用 [as] 来命名该断言，与之前的
    [destruct] 和 [induction] 一样。例如 [assert (0 + n = n) as H]。）
    注意我们用花括号 [{ ... }] 将该断言的证明括了起来。这样不仅方便阅读，
    同时也能在交互使用 Coq 时更容易看出该子目标何时得证。第二个目标
    与之前执行 [assert] 时一样，只是这次在上下文中，我们有了名为 [H] 的前提
    [0 + n = n]。也就是说，[assert] 生成的第一个子目标是我们必须证明的已断言的事实，
    而在第二个子目标中，我们可以使用已断言的事实在一开始尝试证明的事情上取得进展。 *)

(** 另一个 [assert] 的例子... *)

(** 举例来说，假如我们要证明 [(n + m) + (p + q) = (m + n) + (p + q)]。
    [=] 两边唯一不同的就是内层第一个子式中 [+] 的参数 [m] 和 [n] 交换了位置，
    我们似乎可以用加法交换律（[plus_comm]）来改写它。然而，
    [rewrite] 策略并不知道应该作用在 _'哪里'_。本命题中 [+] 用了三次 ，
    结果 [rewrite -> plus_comm] 只对 _'最外层'_ 起了作用... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们只需要将 (m + n) 交换为 (n + m)... 看起来 plus_comm 能搞定！*)
  rewrite -> plus_comm.
  (* 搞不定... Coq 选错了要改写的加法！ *)
Abort.

(** 为了在需要的地方使用 [plus_comm]，我们可以（为此这里讨论的 [m] 和 [n]）
    引入一个局部引理来陈述 [n + m = m + n]，之后用 [plus_comm] 证明它，
    并用它来进行期望的改写。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ################################################################# *)
(** * 形式化证明 vs. 非形式化证明 *)

(** _'“非形式化证明是算法，形式化证明是代码。”'_ *)

(** 数学声明的成功证明由什么构成？这个问题已经困扰了哲学家数千年，
    不过这儿有个还算凑合的定义：数学命题 [P] 的证明是一段书面（或口头）的文本，
    它对 [P] 的真实性进行无可辩驳的论证，逐步说服读者或听者使其确信 [P] 为真。
    也就是说，证明是一种交流行为。

    交流活动会涉及不同类型的读者。一方面，“读者”可以是像 Coq 这样的程序，
    此时灌输的“确信”是 [P] 能够从一个确定的，由形式化逻辑规则组成的集合中
    机械地推导出来，而证明则是指导程序检验这一事实的方法。这种方法就是
    _'形式化'_ 证明。

    另一方面，读者也可以是人类，这种情况下证明可以用英语或其它自然语言写出，
    因此必然是 _'非形式化'_ 的，此时成功的标准不太明确。一个“有效的”证明是让读者
    相信 [P]。但同一个证明可能被很多不同的读者阅读，其中一些人可能会被某种特定
    的表述论证方式说服，而其他人则不会。有些读者太爱钻牛角尖，或者缺乏经验，
    或者只是单纯地过于愚钝；说服他们的唯一方法就是细致入微地进行论证。
    不过熟悉这一领域的读者可能会觉得所有细节都太过繁琐，让他们无法抓住
    整体的思路；他们想要的不过是抓住主要思路，因为相对于事无巨细的描述而言，
    让他们自行补充所需细节更为容易。总之，我们没有一个通用的标准，
    因为没有一种编写非形式化证明的方式能够说服所能顾及的每一个读者。

    然而在实践中，数学家们已经发展出了一套用于描述复杂数学对象的约定和习语，
    这让交流（至少在特定的社区内）变得十分可靠。这种约定俗成的交流形式已然成风，
    它为证明的好坏给出了清晰的判断标准。

    由于我们在本课程中使用 Coq，因此会重度使用形式化证明。但这并不意味着我们
    可以完全忽略掉非形式化的证明过程！形式化证明在很多方面都非常有用，
    不过它们对人类之间的思想交流而言 _'并不'_ 十分高效。 *)

(** 例如，下面是一段加法结合律的证明： *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq 对此表示十分满意。然而人类却很难理解它。我们可以用注释和标号让它
    的结构看上去更清晰一点... *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** ...而且如果你习惯了 Coq，你可能会在脑袋里逐步过一遍策略，并想象出
    每一处上下文和目标栈的状态。不过若证明再复杂一点，那就几乎不可能了。

    一个（迂腐的）数学家可能把证明写成这样： *)

(** - _'定理'_：对于任何 [n]、[m] 和 [p]，

      n + (m + p) = (n + m) + p.

    _'证明'_：对 [n] 使用归纳法。

    - 首先，设 [n = 0]。我们必须证明

        0 + (m + p) = (0 + m) + p.

      此结论可从 [+] 的定义直接得到。

    - 然后，设 [n = S n']，其中

        n' + (m + p) = (n' + m) + p.

      我们必须证明

        (S n') + (m + p) = ((S n') + m) + p.

      根据 [+] 的定义，该式可写成

        S (n' + (m + p)) = S ((n' + m) + p),

      它由归纳假设直接得出。_'证毕'_。 *)

(** 证明的总体形式大体类似，当然这并非偶然：Coq 的设计使其 [induction]
    策略会像数学家写出的标号那样，按相同的顺序生成相同的子目标。但在细节上则有
    明显的不同：形式化证明在某些方面更为明确（例如对 [reflexivity] 的使用），
    但在其它方面则不够明确（特别是 Coq 证明中任何一处的“证明状态”都是完全
    隐含的，而非形式化证明则经常反复告诉读者目前证明进行的状态）。 *)

(** **** 练习：2 星, advanced, recommended (plus_comm_informal)  

    将你对 [plus_comm] 的解答翻译成非形式化证明：

    定理：加法满足交换律。

    Proof: (* 请在此处解答 *)
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_plus_comm_informal : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard, optional (eqb_refl_informal)  

    以 [plus_assoc] 的非形式化证明为范本，写出以下定理的非形式化证明。
    不要只是用中文来解释 Coq 策略！

    定理：对于任何 [n]，均有 [true = n =? n]。

    证明： (* 请在此处解答 *)

    [] *)

(* ################################################################# *)
(** * 更多练习 *)

(** **** 练习：3 星, standard, recommended (mult_comm)  

    用 [assert] 来帮助证明此定理。你应该不需要对 [plus_swap] 进行归纳。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *) Admitted.

(** 现在证明乘法交换律。（你在证明过程中可能需要定义并证明一个独立的辅助定理。
    你可能会用上 [plus_swap]。） *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (more_exercises)  

    找一张纸。对于以下定理，首先请 _'思考'_ (a) 它能否能只用化简和改写来证明，
    (b) 它还需要分类讨论（[destruct]），以及 (c) 它还需要归纳证明。先写下你的
    预判，然后填写下面的证明（你的纸不用交上来，这只是鼓励你先思考再行动！） *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  (* 请在此处解答 *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (eqb_refl)  

    证明以下定理。（把 [true] 放在等式左边可能看起来有点奇怪，不过 Coq 标准库中
    就是这样表示的，我们照做就是。无论按哪个方向改写都一样好用，所以无论我们如何
    表示定理，用起来都没问题。） *)

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (plus_swap')  

    [replace] 策略允许你指定一个具体的要改写的子项和你想要将它改写成的项：
    [replace (t) with (u)] 会将目标中表达式 [t]（的所有副本）替换为表达式 [u]，
    并生成 [t = u] 作为附加的子目标。在简单的 [rewrite] 作用在目标错误的部分上时
    这种做法通常很有用。

   用 [replace] 策略来证明 [plus_swap']，除了无需 [assert (n + m = m + n)]
   外和 [plus_swap] 一样。 *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, recommended (binary_commute)  

    回忆一下你在 [Basics] 中为练习 [binary] 编写的 [incr] 和 [bin_to_nat]
    函数。证明下图可交换。

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    也就是说，一个二进制数先自增然后将它转换为（一进制）自然数，和先将它转换为
    自然数后再自增会产生相同的结果。将你的定理命名为 [bin_to_nat_pres_incr]
    （“pres”即“preserves”的简写，意为“保持原状”）。

    在开始做这个练习之前，将你在 [binary] 练习的解中的定义复制到这里，
    让这个文件可以被单独评分。若你想要更改你的原始定义以便让此属性更易证明，
    请自便！ *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_commute : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, advanced (binary_inverse)  

    This is a further continuation of the previous exercises about
    binary numbers.  You may find you need to go back and change your
    earlier definitions to get things to work here.

    (a) First, write a function to convert natural numbers to binary
        numbers. *)

Fixpoint nat_to_bin (n:nat) : bin
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** Prove that, if we start with any [nat], convert it to binary, and
    convert it back, we get the same [nat] we started with.  (Hint: If
    your definition of [nat_to_bin] involved any extra functions, you
    may need to prove a subsidiary lemma showing how such functions
    relate to [nat_to_bin].) *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  (* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_a : option (nat*string) := None.

(** (b) One might naturally expect that we should also prove the
        opposite direction -- that starting with a binary number,
        converting to a natural, and then back to binary should yield
        the same number we started with.  However, this is not the
        case!  Explain (in a comment) what the problem is. *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_b : option (nat*string) := None.

(** (c) Define a normalization function -- i.e., a function
        [normalize] going directly from [bin] to [bin] (i.e., _not_ by
        converting to [nat] and back) such that, for any binary number
        [b], converting [b] to a natural and then back to binary yields
        [(normalize b)].  Prove it.  (Warning: This part is a bit
        tricky -- you may end up defining several auxiliary lemmas.
        One good way to find out what you need is to start by trying
        to prove the main statement, see where you get stuck, and see
        if you can find a lemma -- perhaps requiring its own inductive
        proof -- that will allow the main proof to make progress.) Don't
        define thi using nat_to_bin and bin_to_nat! *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_binary_inverse_c : option (nat*string) := None.
(** [] *)

(* Fri Jul 19 00:32:19 UTC 2019 *)
