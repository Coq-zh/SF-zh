(** * ProofObjects: 柯里-霍华德对应 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

(** "_'算法是证明的计算性内容。'_"  --Robert Harper *)

(** 前文已讨论过 Coq 既可以用 [nat]、[list] 等归纳类型及其函数_'编程'_，又可
    以用归纳命题（如 [even]）、蕴含式、全称量词等工具_'证明'_程序的性质。我们一直
    以来区别对待此两种用法，在很多情况下确实可以这样。但也有迹象表明在 Coq 中编
    程与证明紧密相关。例如，关键字 [Inductive] 同时用于声明数据类型和命题，以及
    [->] 同时用于描述函数类型和逻辑蕴含式。这可并不是语法上的巧合！事实上，在 Coq
    里面程序和证明几乎就是同一件事情。这一章我们会学习背后的原理。

    我们已经知道这个基础的思想：在Coq里面，可证明性表现为拥有具体的_'证据'_。
    为基本命题构造证明，实则以树状结构表示其证据。

    对于形如 [A -> B] 的蕴含式，其证明为证据_'转化装置（transformer）'_，可将任何
    证明 [A] 的依据转化为 [B] 的证据。所以从根本上来讲，证明仅仅就是操纵证据的程
    序。 *)

(** 试问：如果是证据是数据，那么命题本身是什么？

    答曰：类型也！ *)

(** 回顾一下 [even] 这个性质的形式化定义。  *)

Print even.
(* ==>
  Inductive even : nat -> Prop :=
    | ev_0 : even 0
    | ev_SS : forall n, even n -> even (S (S n)).
*)

(** 试以另一种方式解读“[:]”：以“是……的证明”取代“具有……类型”。例如将定义 [even]
    第二行的 [ev_0 : even 0] 读作“[ev_0] 是 [[even] 0] 的证明”以代替“[ev_0] 具有
    [[even] 0] 类型”。 *)

(** 此处 [:] 既在类型层面表达“具有……类型”，又在命题层面表示“证明了……”。这种双关
    称为_'柯里-霍华德同构（Curry-Howard correspondence）'_。它指出了逻辑与计算之
    间的深层关联：

                 命题           ~  类型
                 证明           ~  数据值

    [Wadler 2015] (in Bib.v) 里有简单的历史和最新的详细介绍可供参考。 *)

(** 该同构启发很多看问题的新方法。首先，对 [ev_SS] 构造子的理解变得更加自然： *)

Check ev_SS.
(* ===> ev_SS : forall n,
                  even n ->
                  even (S (S n)) *)

(** 可以将其读作“[ev_SS] 构造子接受两个参数——数字 [n] 以及命题 [even n]
    的证明——并产生 [even (S (S n))] 的证明。” *)

(** 现在让我们回顾一下之前有关 [even] 的一个证明。 *)

Theorem ev_4 : even 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** 就像是处理普通的数据值和函数一样，我们可以使用 [Print] 指令来查看
    这个证明脚本所产生的_'证据对象 (proof object)'_ *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
     : even 4  *)

(** 实际上，我们也可以不借助脚本_'直接'_写出表达式作为证明。 *)

Check (ev_SS 2 (ev_SS 0 ev_0)).
(* ===> even 4 *)

(** 表达式 [ev_SS 2 (ev_SS 0 ev_0)] 可视为向构造子 [ev_SS] 传入参数 2 和 0
    等参数，以及对应的 [even 2] 与 [even 0] 之依据所构造的证明。或言之，视 [ev_SS]
    为“构造证明”之原语，需要给定一个数字，并进一步提供该数为偶数之依据以构造证明。
    其类型表明了它的功能：

    forall n, even n -> even (S (S n))

    类似地，多态类型 [forall X, list X] 表明可以将 [nil]
    视为从某类型到由该类型元素组成的空列表的函数。 *)

(** 我们在 [Logic] 这一章中已经了解到，我们可以使用函数应用
    的语法来实例化引理中的全称量化变量，也可以使用该语法提供引理所要求
    的假设。例如： *)

Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(* ################################################################# *)
(** * 证明脚本 *)

(** 我们一直在讨论的_'证明对象 (proof objects)'_是Coq如何运作的核心。
    当Coq执行一个证明脚本的时候，在内部，Coq逐渐构造出一个证明对象——
    一个类型是想要证明的命题的项。在 [Proof] 和 [Qed] 之间的策略告诉
    Coq如何构造该项。为了了解这个过程是如何进行的，在下面的策略证明里，
    我们在多个地方使用 [Show Proof] 指令来显示当前证明树的状态。 *)

Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(** 在任意的给定时刻，Coq已经构造了一个包含一个“洞(hole)”（即
    [?Goal] ）的项，并且Coq知道该洞需要什么类型的证据来填补。

    每一个洞对应一个子目标。当没有子目标时，代表证明已经完成。此时，我
    们构造的证明将会以我们在 [Theorem] 里给定的名字被存储在全局环境中。 *)

(** 策略证明非常有用且方便，但是它们并不是必要的：原则上，我们总是能够
    手动构造想要的证据，如下所示。此处我们可以通过 [Definition] （而不
    是 [Theorem]）来直接给这个证据一个全局名称。 *)

Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(** 所有这些构造证明的不同方式，对应的存储在全局环境中的证明是完全一样的。 *)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)

(** **** 练习：2 星, standard (eight_is_even)  

    写出对应 [even 8] 的策略证明和证明对象。 *)

Theorem ev_8 : even 8.
Proof.
  (* 请在此处解答 *) Admitted.

Definition ev_8' : even 8
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(* ################################################################# *)
(** * 量词，蕴含式，函数 *)

(** 在Coq的计算世界里（即所有的数据结构和程序存在的地方），有两种值的
    类型里拥有箭头：_'构造子(Constructors)'_，通过归纳地定义数据类型
    引入，和_'函数(Functions)'_。

    类似地，在Coq的逻辑世界里（即我们运用证明的地方），有两种方式来给
    与蕴含式需要的证据：构造子，通过归纳地定义命题引入，和...函数！
    *)

(** 例如，考虑下列陈述： *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(** 对应 [ev_plus4] 的证明对象是什么？

    我们在寻找一个_'类型(Type)'_是 [forall n, even n -> even (4 + n)] 的表达式——也
    就是说，一个接受两个参数（一个数字和一个证据）并返回一个证据的
    _'函数(Function)'_!

    它的证据对象： *)

Definition ev_plus4' : forall n, even n -> even (4 + n) :=
  fun (n : nat) => fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).

(** 回顾 [fun n => blah] 意味着“一个函数，给定 [n]，产生 [blah]”，
    并且Coq认为 [4 + n] 和 [S (S (S (S n)))] 是同义词，所以另一种写出
    这个定义的方式是： *)

Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.
(* ===>
     : forall n : nat, even n -> even (4 + n) *)

(** 当我们将 [ev_plus4] 证明的命题视为一个函数类型时，我们可以发现一个
    有趣的现象：第二个参数的类型，[even n]，依赖于第一个参数 [n] 的_'值'_。

    虽然这样的_'依赖类型 (Dependent types)'_在传统的编程语言中并不存在，
    但是它们对于编程来说有时候非常有用。最近它们在函数式编程社区里的活
    跃很好地表明了这一点。 *)

(** 注意到蕴含式（[->]）和量化（[forall]）都表示证据上的函数。事实上，他们
    是同一个东西：当我们使用[forall]时没有依赖，就可以简写为当[->]。即，我
    们没有必要给与箭头左边的类型一个名字：

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat -> nat
*)

(** 例如，考虑下列命题： *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : even n), even (n + 2).

(** 这个命题的一个证明项会是一个拥有两个参数的函数：一个数字[n]
    和一个表明[n]是偶数的证据[E]。但是对于这个证据来说，名字[E]并没有
    在[ev_plus2]剩余的陈述里面被使用，所以还专门为它取一个名字并没有意
    义。因此我们可以使用虚拟标志符[_]来替换真实的名字： *)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : even n), even (n + 2).

(** 或者，等同地，我们可以使用更加熟悉的记号： *)

Definition ev_plus2'' : Prop :=
  forall n, even n -> even (n + 2).

(** 总的来说，"[P -> Q]"只是 "[forall (_:P), Q]"的语法糖。 *)

(* ################################################################# *)
(** * 使用策略编程 *)

(** 如果我们可以通过显式地给出项，而不是执行策略脚本，来构造证明，你可
    能会好奇我们是否可以通过_'策略'_，而不是显式地给出项，来构造_'程序'_。
    自然地，答案是可以！ *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

(** 注意到我们通过使用[.]终止了[Definition]，而不是使用[:=]和一个项来
    定义它。这个记号会告诉Coq进入_'证明脚本模式(Proof Scripting
    Mode)'_来构造类型是[nat -> nat]的项。并且，我们通过使用[Defined]而不是
    [Qed]来终止证明；这使得这个定义是_'透明的(Transparent)'_，所以它可
    以在计算中就像正常定义的函数一样被使用。（通过[Qed]定义的对象在计
    算中是不透明的。）

    这个特性主要是在定义拥有依赖类型的函数时非常有用。我们不会在本书中
    详细讨论后者。但是它确实表明了Coq里面基本思想的一致性和正交性。 *)

(* ################################################################# *)
(** * 逻辑联结词作为归纳类型 *)

(** 归纳定义足够用于表达我们目前为止遇到的大多数的联结词。事实上，
    只有全称量化（以及作为特殊情况的蕴含式）是Coq内置的，所有其他的都是被归纳
    定义的。在这一节中我们会看到它们的定义。 *)

Module Props.

(* ================================================================= *)
(** ** 合取 *)

(** 为了证明[P /\ Q]成立，我们必须同时给出[P]和[Q]的证据。因此，我们可
    以合理地将[P /\ Q]的证明对象定义为包含两个证明的元祖：一个是[P]的
    证明，另一个是[Q]的证明。即我们拥有如下定义。 *)

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

(** 注意到这个定义与在章节[Poly]中给出的[prod]定义的类型的相似处；
    唯一的不同之处在于，[prod]的参数是[Type]，而[and]的类型是[Prop]。 *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** 这个定义能够解释为什么[destruct]和[intros]模式能用于一个合取前提。
    情况分析允许我们考虑所有[P /\ Q]可能被证明的方式——只有一种方式（即
    [conj]构造子）。

    类似地，[split]策略能够用于所有只有一个构造子的归
    纳定义命题。特别地，它能够用于[and]： *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

(** 这解释了为什么一直以来我们能够使用策略来操作[and]的归纳定义。我们
    也可以使用模式匹配来用它直接构造证明。例如： *)

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** **** 练习：2 星, standard, optional (conj_fact)  

    构造一个证明对象来证明下列命题。 *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** 析取 *)

(** 析取的归纳定义有两个构造子，分别用于析取的两边： *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

(** 这个声明解释了[destruct]策略在一个析取前提上的行为，产生的子类型和
    [or_introl]以及[or_intror]构造子的形状相匹配。

    又一次地，我们可以不使用策略，直接写出涉及[or]的定义的证明对象。 *)

(** **** 练习：2 星, standard, optional (or_commut'')  

    尝试写下[or_commut]的显式证明对象。（不要使用[Print]来偷看我们已经
    定义的版本！） *)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** 存在量化 *)

(** 为了给出存在量词的证据，我们将一个证据类型[x]和[x]满足性质[P]的证明打包在一起： *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

(** 打包之后的命题可以通过解包操作受益。这里的核心定义是为了用于构造
    [ex P]命题的类型构造器[ex]，其中[P]自身是一个从类型为[A]的证据类型
    值到命题的_'函数(Function)'_。构造子[ex_intro]提供了一个给定
    证据类型[x]和[P x]的证 明，可以构造[ex P]的证据的方式。 *)

(** 我们更加熟悉的类型[exists x, P x]可以转换为一个涉及[ex]的表达式： *)

Check ex (fun n => even n).
(* ===> exists n : nat, even n
        : Prop *)

(** 下面是我们如何定义一个涉及[ex]的显式证明对象： *)

Definition some_nat_is_even : exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** 练习：2 星, standard, optional (ex_ev_Sn)  

    完成下列证明对象的定义： *)

Definition ex_ev_Sn : ex (fun n => even (S n))
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** [True]和[False] *)

(** [True]命题的归纳定义很简单： *)

Inductive True : Prop :=
  | I : True.

(** 它拥有一个构造子（因此[True]的所有证据都是一样的，所以给出一个
    [True]的证明并没有信息量。） *)

(** [False]也一样的简单——事实上，它是如此简单，以致于第一眼看上去像是一个
    语法错误。 *)

Inductive False : Prop := .

(** 也就是说， [False]是一个_'没有'_构造子的归纳类型--即，没有任何方式能
    够构造一个它的证明。 *)

End Props.

(* ################################################################# *)
(** * 相等关系 *)

(** 在Coq里，甚至连相等关系都不是内置的。它拥有如下的归纳定义。（事实上，
    在标准库里的定义是这里给出的定义的轻微变体，前者给出了稍微容易使用
    一些的归纳法则。） *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(** 我们可以这样理解这个定义，给定一个集合[X]，它定义了由[X]的一对值
    ([x]和[y])所索引的“[x]与[y]相等”的一_'系列(Family)'_的命题。只有
    一种方式能够构造该系列中成员的证据：将构造子[eq_refl]应用到类型[X]
    和值[x:X]，产生一个[x]等于[x]的证据。

    其它形如 [eq x y] 的类型中的 [x] 和 [y] 并不相同，因此是非居留的。 *)

(** 我们可以使用[eq_refl]来构造证据，比如说，[2 = 2]。那么我们能否使用
    它来构造证据[1 + 1 = 2]呢？答案是肯定的。事实上，它就是同一个证据！

    原因是如果两个项能够通过一些简单的计算规则_'可转换(convertible)'_ ，
    那么Coq认为两者“相等”。

    这些计算规则，与[Compute]所使用的规则相似，包括函数应用的计算，定
    义的内联，[match]语句的化简。 *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(** 至今为止我们所用来证据相等关系的[reflexivity]策略本质上只是[apply
    eq_refl]的简写。

    在基于策略的相等关系证明中，转换规则通常隐藏在[simpl]的使用后面（在
    其他策略中或显式或隐式，例如[reflexivity]）。

    而在如下的显式证明对象中，你可以直接看到它们： *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

(** **** 练习：2 星, standard (equality__leibniz_equality)  

    相等关系的归纳定义隐含了_'Leibniz相等关系(Leibniz equality)'_：当我们
    说“[x]和[y]相等的时候”，我们意味着所有[x]满足的性质[P]，对于[y]
    来说也满足。 *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, standard, optional (leibniz_equality__equality)  

    请说明，事实上，相等关系的归纳定义和Leibniz相等关系是
    _'等价的(equivalent)'_。 *)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
(* 请在此处解答 *) Admitted.

(** [] *)

End MyEquality.

(* ================================================================= *)
(** ** 再论反演 *)

(** 我们曾经见过[inversion]被同时用于相等关系前提，和关于被归纳定义的命
    题的前提。现在我们明白了实际上它们是同一件事情。那么我们现在可以细
    究一下[inversion]是如何工作的。

    一般来说，[inversion]策略...

    - 接受一个前提[H]，该前提的类型[P]是通过归纳定义的，以及

    - 对于[P]的定义里的每一个构造子[C]，

      - 产生一个新的子目标，在该子目标中我们假设[H]是通过[C]构造的，

      - 作为额外的假设，在子目标的上下文中增加[C]的论据（前提），

      - 将[C]的结论（结果类型）与当前的目标相匹配，计算出为了能够应用[C]而必须成立的一些相等关系，

      - 将这些相等关系加入上下文中（以及，为了方便，在目标中替换它们），以及

      - 如果这些相等关系无法满足（例如，它们涉及到[S n = O]），那么立即解决这个子目标。 *)

(** _'例子'_：如果我们反演一个使用[or]构造的前提，它有两个构
    造子，所以产生了两个子目标。构造子的结论（结果类型，即[P \/ Q]）
    并没有对于[P]和[Q]的形式有任何要求，所以在子目标的上下文中我们不会
    获得额外的相等关系。 *)

(** _'例子'_：如果我们反演一个使用[and]构造的前提，它只有一个构造子，
    所以只产生一个子目标。再一次地，构造子的结论（结果类型，即[P /\ Q]）
    并没有对于[P]和[Q]的形式有任何要求，所以在子目标的上下文中我们不会
    获得额外的相等关系。不过，这个构造子有两个额外的参数，我们能够在子
    目标的上下文中看到它们。 *)

(** _'例子'_：如果我们反演一个使用[eq]构造的前提，它也只有一个构造子，
    所以只产生一个子目标。但是，现在[eq_refl]构造子的形式给我们带来
    的额外的信息：它告诉[eq]的两个参数必须是一样的。于是[inversion]策
    略会将这个事实加入到上下文中。 *)


(* Fri Jul 19 00:32:20 UTC 2019 *)
