(** * MoreStlc: 扩展简单类型 Lambda-演算 *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From Coq Require Import Strings.String.

(* ################################################################# *)
(** * STLC 的简单扩展 *)

(** 简单类型 lambda-演算在理论上有一些有趣的性质，但由于缺乏一些结构使其还不足以成为一个实用的编程语言。

    在本章中，我们引入一些常见的特性来缩小和现实世界中程序语言的距离，这些新的特性
    在类型层面上是简单和直接的。*)

(* ================================================================= *)
(** ** 数值 *)

(** 在 [StlcProp] 一章最后的 [stlc_arith] 练习中，我们看到为 STLC
    添加自然数、常量和原始操作（primitive operation）十分容易的——
    基本只需要将我们在 [Types] 和 [Stlc] 中学到的内容结合起来。
    添加机器整数或浮点数这些类型同样直接，当然语言中数值的规格也会更加精确。*)

(* ================================================================= *)
(** ** Let 绑定 *)

(** 当写一个复杂的表达式时，为一些子表达式命名常常可以避免重复计算和提高可读性。
    多数语言都提供了多种这样的机制。比如，在 OCaml（以及 Coq）中，我们可以写 [let
    x=t1 in t2]，意思是说“首先归约 [t1] 到一个值，并绑定到 [x] 上，同时继续对 [t2]
    归约。”

    我们的 [let] 绑定使用的求值策略和 OCaml 相同，均为标准的_'传值调用（call-by-value）'_，
    也即在对 [let] 的主体（即 [t2]）归约前，被绑定的项（即 [t1]）必须已经完全归约。
    类型规则 [T_Let] 告诉我们可以这样为 [let] 表达式定型：首先计算被绑定项的类型，
    用此类型和对应的绑定名扩展上下文，并在新的上下文中对 [let] 主体定型
    （最后得到的类型便是整个 [let] 表达式的类型）。

    类型规则和自然语言的文本描述了同样的内容，但读者基于在本书中已经学过的内容，
    理解前者应当已经比较容易了。如下： *)

(** 语法：

       t ::=                项
           | ...               （与之前的其他项相同）
           | let x=t in t      let-绑定
*)

(**
    归约规则：

                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 --> [x:=v1]t2

    定型规则：

             Gamma |- t1 \in T1      x|->T1; Gamma |- t2 \in T2
             --------------------------------------------------        (T_Let)
                        Gamma |- let x=t1 in t2 \in T2
*)

(* ================================================================= *)
(** ** 二元组 *)

(** Coq 中的函数式编程经常使用一_'对（pair）'_值，而其类型为_'积类型（product type）'_。

    对二元组（序对）的形式化非常简单，以至于不需要太多讨论。然而，还是让我们看看它的定义，
    以此强调和了解一些常见的模式。*)

(** 在 Coq 里，从一个二元组中提取出值的基本方法是_'模式匹配（pattern matching）'_。
    另一种方法是使用 [fst] 和 [snd]——第一投影和第二投影操作子。
    我们在这里使用第二种方式。举个例子，下面的函数接受自然数的二元组作为参数，
    并返回他们和与差构成的二元组：

       \x : Nat*Nat.
          let sum = x.fst + x.snd in
          let diff = x.fst - x.snd in
          (sum,diff)
*)

(** 为简单类型 lambda-演算添加二元组需要为项添加两种新的形式：创建二元组，写做
    [(t1,t2)]；以及投影操作，写做 [t.fst] 和 [t.snd]，分别用于提取出第一个和
    第二个元素。我们还需要一个新的类型构造子，[T1*T2] 作为 [T1] 和 [T2]
    的_'积（product）'_。*)

(** 语法：

       t ::=                项
           | ...
           | (t,t)             二元组
           | t.fst             第一个元素
           | t.snd             第二个元素

       v ::=                值
           | ...
           | (v,v)             二元组值

       T ::=                类型
           | ...
           | T * T             积类型
*)

(** 我们需要几个新的归约规则来描述二元组和投影操作的行为。

                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                              t1 --> t1'
                          ------------------                          (ST_Fst1)
                          t1.fst --> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                              t1 --> t1'
                          ------------------                          (ST_Snd1)
                          t1.snd --> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2
*)

(** 规则 [ST_FstPair] 和 [ST_SndPair] 是说，我们可以对完全归约的二元组
    取其第一个元素或第二个元素。同余规则 [ST_Fst1] 和 [ST_Snd1] 则是说，
    在被投影的二元组还没有完全归约时，我们可以在投影下允许对二元组归约。
    [ST_Pair1] 和 [ST_Pair2] 则对二元组的某一部分归约：分别是左边的部分，以及
    当左边的部分是值时对右边的部分归约。在这两个规则中，我们使用元变量
    [v] 和 [t] 来强制对二元组实现从左向右的求值策略。（请注意，其中隐含的约定是 [v]
    或 [v1] 这样的元变量仅指值。）我们同样添加了对二元组值的定义，即 [(v1,v2)]
    是一个值。二元组的成员必须是值，这一点保证了当二元组作为参数传入一个函数时已经
    完全归约了。*)

(** 二元组和投影的类型规则十分直接。 

               Gamma |- t1 \in T1     Gamma |- t2 \in T2
               -----------------------------------------               (T_Pair)
                       Gamma |- (t1,t2) \in T1*T2

                        Gamma |- t \in T1*T2
                        ---------------------                          (T_Fst)
                        Gamma |- t.fst \in T1

                        Gamma |- t \in T1*T2
                        ---------------------                          (T_Snd)
                        Gamma |- t.snd \in T2
*)

(** [T_Pair] 是说如果 [t1] 有类型 [T1] 且 [t2] 有类型 [T2]，
    那么 [(t1,t2)] 有类型 [T1*T2] 。相反，[T_Fst] 和 [T_Snd] 告诉我们，
   如果 [t1] 为积类型 [T1*T2]（即，如果 [t1] 会归约为一个二元组），
   那么二元组的投影的类型为 [T1] 和 [T2]。*)

(* ================================================================= *)
(** ** 单元素类型 *)

(** 另一个在 ML 语言家族中经常出现的基础类型是只含有一个元素的类型（singleton type），即 [Unit]。

    它只含有一个常量项 [unit]（以小写 [u] 开头），以及一个类型规则使 [unit] 成为
    [Unit] 的一个元素。我们同时添加 [unit] 到可作为值的项的集合中，确实，[unit]
    是 [Unit] 类型的表达式唯一可能的归约结果。 *)

(** 语法：

       t ::=                Terms
           | ...               (other terms same as before)
           | unit              unit

       v ::=                Values
           | ...
           | unit              unit value

       T ::=                Types
           | ...
           | Unit              unit type

    定型规则：

                         ----------------------                        (T_Unit)
                         Gamma |- unit \in Unit
*)

(** 看起来似乎有些奇怪，我们为什么要定义只含有一个元素的类型呢？
    毕竟，难道不是每个计算都不会在这样的类型中居留吗？

    这是个好问题，而且确实在 STLC 中 [Unit] 类型并不是特别重要（尽管后面我们会看
    到它的两个用处）。在更丰富的语言中，使用 [Unit] 类型来处理_'副作用（side effect）'_
    会很方便，例如改写变量或指针的赋值语句、异常以及其他非局部控制结构等情形。
    在这样的语言中，[Unit] 类型为仅有副作用的表达式提供了一个方便的类型。*)

(* ================================================================= *)
(** ** 和类型 *)

(** 一些程序需要处理具有两种不同形式的值。比如说，在一个大学数据库中中我们想要根据名字
    _'或'_识别号码来搜索某个学生。这个搜索函数可以返回匹配到的值，_'或'_返回一个错误代码。

    有很多二元_'和类型（sum type）'_（有时候也叫做_'不交并（disjoint union）'_）
    的具体例子，他们描述了从一个或两个给定类型的值的集合，例如：

       Nat + Bool

    我们在创建这些类型的值时，会为值_'标记（tagging）'_上其成分类型。
    比如说，如果 [n] 是自然数，那么 [inl n] 是 [Nat+Bool] 的一个元素；
    类似地，如果 [b] 的类型为 [Bool]，那么 [inr b] 是 [Nat+Bool]
    的一个元素。
    如果把标签 [inl] 和 [inr] 看作函数，其类型解释了他们的名字：

       inl \in Nat  -> Nat + Bool
       inr \in Bool -> Nat + Bool

    这两个函数分别将 [Nat] 或 [Bool] 的元素“注入”进和类型 [Nat+Bool]
    的左成分或右成分中。（但其实我们不必将其作为函数形式化：[inl] 和 [inr]
    是关键字，而且  [inl t] 和 [inr t] 是基本的语法形式，而非函数应用。） *)

(** 一般来说，被 [inl] 标记的 [T1] 的元素加上被 [inr]
    标记的 [T2] 的元素一同构成了 [T1 + T2] 的元素。 *)

(** 我们之前在 Coq 编程中见过，和类型的一个重要用途是传递错误：

      div \in Nat -> Nat -> (Nat + Unit)
      div =
        \x:Nat. \y:Nat.
          test iszero y then
            inr unit
          else
            inl ...

    事实上，上面的 [Nat + Unit] 类型与 Coq 中的 [option nat]
    类型是同构的——也即，我们很容易写出他们的转换函数。 *)

(** 为了_'使用'_和类型和元素，我们引入 [case] 语句（Coq 中 [match]
    的非常简化版）用于解构他们。比如说，下面的程序将 [Nat+Bool] 的值转为了 [Nat]：

    getNat \in Nat+Bool -> Nat
    getNat =
      \x:Nat+Bool.
        case x of
          inl n => n
        | inr b => test b then 1 else 0

    更加形式化地讲…… *)

(** 语法：

       t ::=                项
           | ...               （和前面一样的其它项）
           | inl T t           左标记
           | inr T t           右标记
           | case t of         模式匹配
               inl x => t
             | inr x => t

       v ::=                值
           | ...
           | inl T v           标记过的值（左）
           | inr T v           标记过的值（右）

       T ::=                类型
           | ...
           | T + T             和类型
*)

(** 归约规则：

                               t1 --> t1'
                        ------------------------                       (ST_Inl)
                        inl T2 t1 --> inl T2 t1'

                               t2 --> t2'
                        ------------------------                       (ST_Inr)
                        inr T1 t2 --> inr T1 t2'

                               t0 --> t0'
               -------------------------------------------            (ST_Case)
                case t0 of inl x1 => t1 | inr x2 => t2 -->
               case t0' of inl x1 => t1 | inr x2 => t2

            -----------------------------------------------        (ST_CaseInl)
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2
                           -->  [x1:=v1]t1

            -----------------------------------------------        (ST_CaseInr)
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2
                           -->  [x2:=v1]t2
*)

(** 定型规则：

                          Gamma |- t1 \in T1
                   ------------------------------                       (T_Inl)
                   Gamma |- inl T2 t1 \in T1 + T2

                          Gamma |- t2 \in T2
                   -------------------------------                      (T_Inr)
                    Gamma |- inr T1 t2 \in T1 + T2

                        Gamma |- t \in T1+T2
                     x1|->T1; Gamma |- t1 \in T
                     x2|->T2; Gamma |- t2 \in T
         ----------------------------------------------------          (T_Case)
         Gamma |- case t of inl x1 => t1 | inr x2 => t2 \in T

    为了让类型关系简单一点，在 [inl] 和 [inr] 规则中我们使用了类型注释，我们在处理
    函数的类型时也是这么做的。*)

(** 如果没有这额外的类型信息，一旦我们确定了 [t1] 为类型 [T1]，类型规则
    [T_Inl] 则必须有能力为 [inl t1] 推导出类型 [T1 + T2]，而其中 [T2]
    可为任意类型。比如说，我们可以同时推导出 [inl 5 : Nat + Nat] 和
    [inl 5 : Nat + Bool]（以及无数个这样的类型）。这一特性（技术上说，
    是类型唯一性的丧失）意味着我们无法像之前处理其他特性那样仅仅通过“自底向上地
    阅读类型规则”来构造出类型检查的算法。

    有很多种方式处理这个难题。最简单的方法，也是我们在这里采用的，就是要求程序员
    在注入时显式地提供和类型“另一侧”的类型。这对程序员会产生一些负担（因此很多
    现实语言采用了其他方法），但这种方法易于理解和形式化。*)

(* ================================================================= *)
(** ** 列表 *)

(** 我们可以将之前学过的类型归结为两类：例如 [Bool] 这样的_'基本类型'_；
    以及例如 [->] 和 [*] 这样的_'类型构造子'_，用于从已有的类型构造新的类型。
    另一个非常有用的类型构造子是 [List]。对于每个类型 [T]，类型 [List T]
    表示元素类型为 [T] 的有限长列表。

    原则上，我们可以用二元组、和类型与_'递归'_类型编码出列表。但为递归类型给出
    其语义并不直接。因此，我们直接将列表作为一个特殊类型加以讨论。

    下面我们给出列表的语法，语义和类型规则。这些列表操作基本与 Coq 中的相同，
    除了 [nil] 中类型注解是强制的，而 [cons] 而不需要类型注解。我们使用 [lcase]
    来解构列表，以此可以用于提取出列表的 [head] 等。*)

(** 例如，下面的函数计算了一个数值列表的前两个元素之和：

      \x:List Nat.
      lcase x of nil   => 0
               | a::x' => lcase x' of nil    => a
                                    | b::x'' => a+b

    语法：

       t ::=                项
           | ...
           | nil T
           | cons t t
           | lcase t of nil  => t
                      | x::x => t

       v ::=                值
           | ...
           | nil T             nil 值
           | cons v v          cons 值

       T ::=                类型
           | ...
           | List T            T 类型列表
*)

(** 归约规则：

                                t1 --> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 --> cons t1' t2

                                t2 --> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 --> cons v1 t2'

                              t1 --> t1'
                -------------------------------------------         (ST_Lcase1)
                 (lcase t1 of nil => t2 | xh::xt => t3) -->
                (lcase t1' of nil => t2 | xh::xt => t3)

               -----------------------------------------          (ST_LcaseNil)
               (lcase nil T of nil => t2 | xh::xt => t3)
                                --> t2

            ------------------------------------------------     (ST_LcaseCons)
            (lcase (cons vh vt) of nil => t2 | xh::xt => t3)
                          --> [xh:=vh,xt:=vt]t3
*)

(** 定型规则：

                        -------------------------                       (T_Nil)
                        Gamma |- nil T \in List T

             Gamma |- t1 \in T      Gamma |- t2 \in List T
             ---------------------------------------------             (T_Cons)
                    Gamma |- cons t1 t2 \in List T

                        Gamma |- t1 \in List T1
                        Gamma |- t2 \in T
                (h|->T1; t|->List T1; Gamma) |- t3 \in T
          ---------------------------------------------------         (T_Lcase)
          Gamma |- (lcase t1 of nil => t2 | h::t => t3) \in T
*)

(* ================================================================= *)
(** ** 一般递归 *)

(** 另一个在多数语言（包括 Coq）中都会出现的功能是定义递归函数。例如，我们可以用
    如下方式定义阶乘函数：

      fact = \x:Nat.
                test x=0 then 1 else x * (fact (pred x)))

   请注意绑定的右侧使用了绑定左侧的变量名——这在我们之前的 [let] 中是不被允许的。

   直接形式化这种“递归定义”机制是可行的，但也需要一些额外的努力：特别是，在 [step]
   关系中，我们需要给递归函数的定义传递一个“环境”。*)

(** 还有另外一种有点啰嗦但一样强大的方式来形式化递归函数，
    这种方式更加直接：我们不直接写递归的定义，而是定义一个叫做 [fix]
    的_'不动点算子（fixed-point operator）'_，它会在归约时“展开”定义右侧表达式中
    出现的递归定义。

    比如说，以下程序

      fact = \x:Nat.
                test x=0 then 1 else x * (fact (pred x)))

    可以改写为：

      fact =
          fix
            (\f:Nat->Nat.
               \x:Nat.
                  test x=0 then 1 else x * (f (pred x)))

    我们可用如下方式把前者转换为后者：

      - 在 [fact] 的定义的右侧表达式中，替换递归引用的 [fact] 为一个新的变量 [f]。

      - 在最开始为抽象添加一个参数 [f]，以及其合适的类型注解。（因为我们用 [f]
        替换了类型为 [Nat->Nat] 的 [fact]，我们也要求 [f] 有相同的类型。）
        新的抽象有类型 [(Nat->Nat) -> (Nat->Nat)]。

      - 对这个抽象应用 [fix]。这个应用的类型为 [Nat->Nat]。

      - 在其他地方，像使用普通的 [let] 绑定一样使用 [fact]。
*)

(** 可以把被传入 [fix] 的高阶函数 [f] 理解为一个 [fact] 函数的_'生成器（generator）'_：
    如果 [f] 被应用于一个函数，且这个函数“近似地”描述了 [fact] 对至多某个数 [n] 的行为
    （也即，一个仅会对小于或等于 [n] 的输入上返回正确结果的函数，但是我们并不在乎其在大于
    [n] 的输入上的结果），那么 [f] 返回一个稍微好一点的 [fact] 的近似——一个对至多
    [n+1] 会返回正确结果的函数。对这个生成器应用 [fix] 会返回它的_'不动点'_，也即一个对
    所有输入 [n] 都有正确结果的函数。

    （“不动点”在这里的含义与数学上的不动点是完全相同的，也即函数 [f] 的一个不动点
    是对于输入 [x] 有 [f(x) = x]。这里，类型为 [(Nat->Nat)->(Nat->Nat)]
    的函数 [F] 的一个不动点是类型为 [Nat->Nat] 的函数 [f]，使得 [F f] 与 [f]
    的行为完全相同。） *)

(** 语法：

       t ::=                项
           | ...
           | fix t             不动点算子

   归约规则：

                                t1 --> t1'
                            ------------------                        (ST_Fix1)
                            fix t1 --> fix t1'

               --------------------------------------------         (ST_FixAbs)
               fix (\xf:T1.t2) --> [xf:=fix (\xf:T1.t2)] t2

   定型规则：

                           Gamma |- t1 \in T1->T1
                           ----------------------                       (T_Fix)
                           Gamma |- fix t1 \in T1
*)

(** 让我们以 [fact 3 = fix F 3] 为例看看 [ST_FixAbs] 是如何工作的，其中

    F = (\f. \x. test x=0 then 1 else x * (f (pred x)))

    （简洁起见，我们省略了类型注解）。

    fix F 3

[-->] [ST_FixAbs] + [ST_App1]

    (\x. test x=0 then 1 else x * (fix F (pred x))) 3

[-->] [ST_AppAbs]

    test 3=0 then 1 else 3 * (fix F (pred 3))

[-->] [ST_Test0_Nonzero]

    3 * (fix F (pred 3))

[-->] [ST_FixAbs + ST_Mult2]

    3 * ((\x. test x=0 then 1 else x * (fix F (pred x))) (pred 3))

[-->] [ST_PredNat + ST_Mult2 + ST_App2]

    3 * ((\x. test x=0 then 1 else x * (fix F (pred x))) 2)

[-->] [ST_AppAbs + ST_Mult2]

    3 * (test 2=0 then 1 else 2 * (fix F (pred 2)))

[-->] [ST_Test0_Nonzero + ST_Mult2]

    3 * (2 * (fix F (pred 2)))

[-->] [ST_FixAbs + 2 x ST_Mult2]

    3 * (2 * ((\x. test x=0 then 1 else x * (fix F (pred x))) (pred 2)))

[-->] [ST_PredNat + 2 x ST_Mult2 + ST_App2]

    3 * (2 * ((\x. test x=0 then 1 else x * (fix F (pred x))) 1))

[-->] [ST_AppAbs + 2 x ST_Mult2]

    3 * (2 * (test 1=0 then 1 else 1 * (fix F (pred 1))))

[-->] [ST_Test0_Nonzero + 2 x ST_Mult2]

    3 * (2 * (1 * (fix F (pred 1))))

[-->] [ST_FixAbs + 3 x ST_Mult2]

    3 * (2 * (1 * ((\x. test x=0 then 1 else x * (fix F (pred x))) (pred 1))))

[-->] [ST_PredNat + 3 x ST_Mult2 + ST_App2]

    3 * (2 * (1 * ((\x. test x=0 then 1 else x * (fix F (pred x))) 0)))

[-->] [ST_AppAbs + 3 x ST_Mult2]

    3 * (2 * (1 * (test 0=0 then 1 else 0 * (fix F (pred 0)))))

[-->] [ST_Test0Zero + 3 x ST_Mult2]

    3 * (2 * (1 * 1))

[-->] [ST_MultNats + 2 x ST_Mult2]

    3 * (2 * 1)

[-->] [ST_MultNats + ST_Mult2]

    3 * 2

[-->] [ST_MultNats]

    6
*)

(** 特别重要的一点是，不同于 Coq 中的 [Fixpoint] 定义，
    [fix] 并不会保证所定义的函数一定停机。*)

(** **** 练习：1 星, standard, optional (halve_fix)  

    请将下面非形式化的定义使用 [fix] 写出：

      halve =
        \x:Nat.
           test x=0 then 0
           else test (pred x)=0 then 0
           else 1 + (halve (pred (pred x)))

(* 请在此处解答 *)

    [] *)

(** **** 练习：1 星, standard, optional (fact_steps)  

    请分步骤写下 [fact 1] 如何归约为正规式（假定有一般算数操作的归约规则）。

    (* 请在此处解答 *)

    [] *)

(** 对任意类型 [T]，构造类型为 [T->T] 的函数的不动点的能力带了了一些令人惊讶的推论。
    特别是，这意味着_'每个'_类型都存在某个项。我们可以观察到，对每个类型 [T]，
    我们可以定义项

    fix (\x:T.x)

    由规则 [T_Fix] 和 [T_Abs]，这个项的类型为 [T]。由规则 [ST_FixAbs]，
    这个项重复地归约为它自身。因此，它是类型 [T] 的_'不停机项（diverging element）'_。

    从更为实用的角度，下面提供一个使用 [fix] 定义两个参数的递归函数：

    equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             test m=0 then iszero n
             else test n=0 then fls
             else eq (pred m) (pred n))

    最后的例子展示了如何用 [fix] 定一个_'二元组'_的递归函数（规则 [T_Fix]
    中的 [T1] 并不需要函数类型）：

      evenodd =
        fix
          (\eo: (Nat->Bool * Nat->Bool).
             let e = \n:Nat. test n=0 then tru else eo.snd (pred n) in
             let o = \n:Nat. test n=0 then fls else eo.fst (pred n) in
             (e,o))

      even = evenodd.fst
      odd  = evenodd.snd
*)

(* ================================================================= *)
(** ** 字段组 *)

(** 作为 STLC 最后的一个基础扩展，让我们简要地学习一下如何定义_'字段组（record）'_
    及其类型。直观地说，字段组可以通过从两个方面一般化二元组来得到：他们是 n
    元（而不仅仅是二元）的而且可以通过_'标签（label）'_（而不仅仅是位置）来访问字段。 *)

(** Syntax:

       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record
           | t.i                         projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
*)

(** 对二元组的一般化是很容易的。但是需要提醒的是，这里描述的方式要比之前章节中的
   非形式语法_'更加'_非形式：我们多处使用了“[...]”来描述“任意数量的某项”，
   我们还省略了“字段组的标签不应当重复”这个附加条件。*)

(**
   归约规则：

                              ti --> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti , ...}
                 --> {i1=v1, ..., im=vm, in=ti', ...}

                              t1 --> t1'
                            --------------                           (ST_Proj1)
                            t1.i --> t1'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i --> vi

    再次提醒，这些规则是非形式化的。比如说，第一个规则应当被读做“如果 [ti]
   是最左边的非值字段，且如果 [ti] 前进一步归约到 [ti']，那么整个字段组归约为……”。
   最后一个规则的意思是说应当只有一个名字为 [i] 的字段，而其他的字段必须指向值。*)

(**
   类型规则同样简单：

            Gamma |- t1 \in T1     ...     Gamma |- tn \in Tn
          ----------------------------------------------------          (T_Rcd)
          Gamma |- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn}

                    Gamma |- t \in {..., i:Ti, ...}
                    -------------------------------                    (T_Proj)
                          Gamma |- t.i \in Ti
*)

(** 有许多种方式来形式化上面的描述。

      - 我们可以直接形式化语法结构和推断规则，并尽量与我们上面给出的非形式化描述保持相同。
        这在概念上来讲十分直接，当我们开发一个真正的编译器时，也会是我们的选择（特别是，
        它允许我们给出程序员易读的错误信息）。但是这些形式化的规则并不是十分容易和其他
        部分配合，因为上面出现的 [...] 需要被替换为显式的量词（quantification）
        或推导式（comprehension）。基于这个原因，本章最后的扩展练习中并没有包括字段组。
        （这里非形式化地讨论字段组仍然非常有用，因为它为 [Sub]
        一章中对子类型的讨论提供了基础。）

      - 此外，我们还可以用一种更简单的方式来表达字段组——比如说，相比与使用单一的构造子
        直接地构造整个字段组，我们可以使用二元的表示，其中一个构造子表示空字段组，
        另一个用于为已有的字段组添加一个新的字段。如果我们主要的兴趣在于学习带字段组
        的演算的元理论，那么这种方式的定义和证明更加简单优雅。在 [Records]
        一章中我们会学习此种处理方式。

      - 最后，如果我们想的话，也可以通过使用二元组和积类型构造复杂的表达式并模拟字段组
        来完全避免形式化字段组。在下一节中我们简要地描述这种方式。 *)

(* ----------------------------------------------------------------- *)
(** *** 编码字段组（选读） *)

(** 让我们看看如何只使用二元组和 [unit] 来编码字段组。（这种聪明的编码来自于
    Luca Cardelli，基于它也会扩展到具有子类型的系统观察。）

    首先，我们可以用嵌套的二元组和 [unit] 值来编码任意大小的_'元组'_。为了避免重载
    已有的二元组记法 [(t1,t2)]，我们使用无标签的花括号来表示元组，例如 [{}]
    是空元组，[{5}] 是只有一个元素的元组，[{5,6}] 是二元组，
    而 [{5,6,7}] 是一个三元组，以此类推。

      {}                 ---->  unit
      {t1, t2, ..., tn}  ---->  (t1, trest)
                                其中 {t2, ..., tn} ----> trest

    类似地，我们可以用积类型来表示元组类型：

      {}                 ---->  Unit
      {T1, T2, ..., Tn}  ---->  T1 * TRest
                                其中 {T2, ..., Tn} ----> TRest

    从元组中投影出元素的操作可以被编码为连续使用多次（或零次）第二投影操作，
    最后使用第一投影操作：

      t.0 ----> t.fst t.(n+1) ----> (t.snd).n

    下一步，假设在字段组的标签上存在某种全序，那么我们可以为每个标签关联一个唯一的自然数。
    这个数被乘坐标签的_'位置'_。比如说，我们可以像下面这样指派位置：

      标签     位置
      a       0
      b       1
      c       2
      ...     ...
      bar     1395
      ...     ...
      foo     4460
      ...     ...

    我们根据字段的位置对他们排序，并使用这些位置来把字段组编码为元组（也即，嵌套的二元组）。
    例如：

      {a=5,b=6} ----> {5,6} {a=5,c=7} ----> {5,unit,7} {c=7,a=5} ---->
      {5,unit,7} {c=5,b=3} ----> {unit,3,5} {f=8,c=5,a=7} ---->
      {7,unit,5,unit,unit,8} {f=8,c=5} ----> {unit,unit,5,unit,unit,8}

    请注意，每个字段都出现在他们标签所关联的位置，因此元组的大小取决与有最高位置的标签，
    我们把未使用的位置填充为 [unit] 值。

    我们在编码字段组类型时使用同样的方式：

      {a:Nat,b:Nat} ----> {Nat,Nat} {c:Nat,a:Nat} ----> {Nat,Unit,Nat}
      {f:Nat,c:Nat} ----> {Unit,Unit,Nat,Unit,Unit,Nat}

    最后，字段组投影被编码为在正确的位置上对元组投影：

      t.l ----> t.(l 的位置)

    我们不难用这种编码来验证以“直接”形式表达的字段组的类型规则。（除了我们编码的是排序后的字段，
    剩下的归约规则几乎已经被验证了。） *)

(** 当然，如果我们碰巧使用了标签 [foo]，那么这种编码方式并不是十分高效。
    但是这也并没有想象的那样糟糕：比如说，如果假设我们的编译器可以在同一时间获得
    完整的程序，那么我们可以为经常使用的标签_'选择'_较小的位置。的确，一些成熟
    的编译器所做的正是如此。*)

(* ----------------------------------------------------------------- *)
(** *** 变种类型（选读） *)

(** 正如同积类型可以泛化为字段组，和类型也可以泛化为 n 元标签类型，称作_'变种类型（variants）'_。
    我们可以把其类型写做 [<l1:T1,l2:T2,...ln:Tn>] 而非 [T1+T2]，其中 [l1]，[l2]，[...]
    是字段的标签，用于构造实例以及解构时分类讨论。

    这些 n 元变种类型提供了足够的机制来构造任意的归纳数据类型，比如列表和树。
    唯一缺少的东西是在类型定义中_'递归（recursion）'_。在本书中我们不会讲解这些，
    但在许多其他的教材中可以学习到他们，例如 Types and Programming Languages
    一书 [Pierce 2002] (in Bib.v)。*)

(* ################################################################# *)
(** * 练习：形式化以上扩展 *)

Module STLCExtended.

(** **** 练习：3 星, standard (STLCE_definitions)  

    在接下来的一系列练习中，你将会形式化本章中描述的一些扩展。
    我们提供了必要的项和类型的语法，以及一些例子用于测试你的定义是否工作。
    你需要完成剩下的定义，并相应地扩展证明。

    作为开始，我们提供了下列实现：
     - 数值
     - 和
     - 列表
     - 项

    你需要完成的实现有：
     - 二元组
     - let（涉及到变量绑定）
     - [fix]

    一个比较好的策略是一次完成一个扩展，分两部完成全部练习，
    而不是尝试一次从头到尾完成本文件中所有的练习。
    对每个定义或证明，首先仔细阅读已经提供的部分，可回顾 [Stlc]
    一章中的文本，并展开嵌套的注释复习细节。*)

(* ----------------------------------------------------------------- *)
(** *** 语法 *)

Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat  : ty
  | Sum  : ty -> ty -> ty
  | List : ty -> ty
  | Unit : ty
  | Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* 纯 STLC *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (* 数值 *)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | mlt : tm -> tm -> tm
  | test0  : tm -> tm -> tm -> tm
  (* 和 *)
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* 列表 *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [lcase t1 of | nil => t2 | x::y => t3] *)
  (* unit *)
  | unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
  (* let *)
  | tlet : string -> tm -> tm -> tm
         (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tfix  : tm -> tm.

(** 请注意，简洁起见，我们省略了布尔值，但提供了 [test0] 用于测试 0 值和作为条件语句。
    也即，当有：

       test x = 0 then ... else ...

    我们可以写做：

       test0 x then ... else ...
*)

(* ----------------------------------------------------------------- *)
(** *** 替换 *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  (* numbers *)
  | const n =>
      const n
  | scc t1 =>
      scc (subst x s t1)
  | prd t1 =>
      prd (subst x s t1)
  | mlt t1 t2 =>
      mlt (subst x s t1) (subst x s t2)
  | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)
  (* sums *)
  | tinl T t1 =>
      tinl T (subst x s t1)
  | tinr T t1 =>
      tinr T (subst x s t1)
  | tcase t0 y1 t1 y2 t2 =>
      tcase (subst x s t0)
         y1 (if eqb_string x y1 then t1 else (subst x s t1))
         y2 (if eqb_string x y2 then t2 else (subst x s t2))
  (* lists *)
  | tnil T =>
      tnil T
  | tcons t1 t2 =>
      tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
      tlcase (subst x s t1) (subst x s t2) y1 y2
        (if eqb_string x y1 then
           t3
         else if eqb_string x y2 then t3
              else (subst x s t3))
  (* unit *)
  | unit => unit

  (* Complete the following cases. *)

  (* pairs *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)
  | _ => t  (* ... and delete this line when you finish the exercise *)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ----------------------------------------------------------------- *)
(** *** 归约 *)

(** 下面我们定义语言的值。 *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  (* 数值是值： *)
  | v_nat : forall n1,
      value (const n1)
  (* 带标记的值也是值： *)
  | v_inl : forall v T,
      value v ->
      value (tinl T v)
  | v_inr : forall v T,
      value v ->
      value (tinr T v)
  (* 列表是值当且仅当其头部（head）和尾部（tail）均为值：*)
  | v_lnil : forall T, value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl)
  (* A unit is always a value *)
  | v_unit : value unit
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (pair v1 v2).

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  (* 数值 *)
  | ST_Succ1 : forall t1 t1',
       t1 --> t1' ->
       (scc t1) --> (scc t1')
  | ST_SuccNat : forall n1,
       (scc (const n1)) --> (const (S n1))
  | ST_Pred : forall t1 t1',
       t1 --> t1' ->
       (prd t1) --> (prd t1')
  | ST_PredNat : forall n1,
       (prd (const n1)) --> (const (pred n1))
  | ST_Mult1 : forall t1 t1' t2,
       t1 --> t1' ->
       (mlt t1 t2) --> (mlt t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (mlt v1 t2) --> (mlt v1 t2')
  | ST_Mulconsts : forall n1 n2,
       (mlt (const n1) (const n2)) --> (const (mult n1 n2))
  | ST_Test01 : forall t1 t1' t2 t3,
       t1 --> t1' ->
       (test0 t1 t2 t3) --> (test0 t1' t2 t3)
  | ST_Test0Zero : forall t2 t3,
       (test0 (const 0) t2 t3) --> t2
  | ST_Test0Nonzero : forall n t2 t3,
       (test0 (const (S n)) t2 t3) --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T,
        t1 --> t1' ->
        (tinl T t1) --> (tinl T t1')
  | ST_Inr : forall t1 t1' T,
        t1 --> t1' ->
        (tinr T t1) --> (tinr T t1')
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        (tcase t0 x1 t1 x2 t2) --> (tcase t0' x1 t1 x2 t2)
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinl T v0) x1 t1 x2 t2) --> [x1:=v0]t1
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinr T v0) x1 t1 x2 t2) --> [x2:=v0]t2
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       (tcons t1 t2) --> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (tcons v1 t2) --> (tcons v1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       (tlcase t1 t2 x1 x2 t3) --> (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
       (tlcase (tnil T) t2 x1 x2 t3) --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       (tlcase (tcons v1 vl) t2 x1 x2 t3)
         --> (subst x2 vl (subst x1 v1 t3))

  (* Add rules for the following extensions. *)

  (* 二元组 *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)

where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

(* ----------------------------------------------------------------- *)
(** *** 定型 *)

Definition context := partial_map ty.

(** 下面我们定义类型规则，这基本上是直接将推断规则翻译一下。 *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* 纯 STLC 的定型规则 *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (var x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (app t1 t2) \in T2
  (* 数值 *)
  | T_Nat : forall Gamma n1,
      Gamma |- (const n1) \in Nat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 \in Nat ->
      Gamma |- (scc t1) \in Nat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 \in Nat ->
      Gamma |- (prd t1) \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- (mlt t1 t2) \in Nat
  | T_Test0 : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (test0 t1 t2 t3) \in T1
  (* 和 *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (tinl T2 t1) \in (Sum T1 T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (tinr T1 t2) \in (Sum T1 T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
      Gamma |- t0 \in (Sum T1 T2) ->
      (update Gamma x1 T1) |- t1 \in T ->
      (update Gamma x2 T2) |- t2 \in T ->
      Gamma |- (tcase t0 x1 t1 x2 t2) \in T
  (* 列表 *)
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) \in (List T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (tcons t1 t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (List T1) ->
      Gamma |- t2 \in T2 ->
      (update (update Gamma x2 (List T1)) x1 T1) |- t3 \in T2 ->
      Gamma |- (tlcase t1 t2 x1 x2 t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_extensions_definition : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 例子 *)

(** **** 练习：3 星, standard (STLCE_examples)  

    本节形式化了一些上文中出现的例子（以及一些其他的例子）。

    只要你为通过测试实现了足够的定义，就取消证明的注释并将 [Admitted] 替换为 [Qed]。

    最开始我们会专注于某些特性，而在开始证明这些特性之前，你可以用一些例子先来
    测试一下你的定义是否合理。后面的例子会整合全部的特性，因此你需要在完成所有的
    定义后再阅读这部分。*)

Module Examples.

(* ----------------------------------------------------------------- *)
(** *** 基础 *)

(** 首先，让我们定义几个变量： *)

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

(** 下面，我们为 Coq 提供一些提示来自动地搜索类型导出式。你不需要理解这部分的全部细节——
    大概看一下便可，当你需要自己扩展 [auto] 时可再回过头来学习。

    下面的 [Hint] 定义是说，当 [auto] 遇到一个形如 [(Gamma |- (app e1 e1) \in T)]
    的目标时，它应当考虑使用 [eapply T_App]，并为中间的类型 T1 留下一个存在变量。
    [lcase] 与此类似。这个变量在后面为 [e1] 和 [e2] 搜索类型导出式的过程中会被填补。
    我们还引入一个提示用于搜索形如等式的证明目标；这对使用 [T_Var] 的情景非常有用
    （其含有一个等式作为前提条件）。 *)

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

(* ----------------------------------------------------------------- *)
(** *** 数值 *)

Module Numtest.

(* test0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition test :=
  test0
    (prd
      (scc
        (prd
          (mlt
            (const 2)
            (const 0)))))
    (const 5)
    (const 6).

Example typechecks :
  empty |- test \in Nat.
Proof.
  unfold test.
  (* 这里的类型导出式非常深，因此我们需要将 [auto] 的最大搜索深度从 5 改为 10。 *)
  auto 10.
(* 请在此处解答 *) Admitted.

Example numtest_reduces :
  test -->* const 5.
Proof.
(* 
  unfold test. normalize.
*)
(* 请在此处解答 *) Admitted.

End Numtest.

(* ----------------------------------------------------------------- *)
(** *** 积 *)

Module Prodtest.

(* ((5,6),7).fst.snd *)
Definition test :=
  snd
    (fst
      (pair
        (pair
          (const 5)
          (const 6))
        (const 7))).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. (* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  test -->* const 6.
Proof.
(* 
  unfold test. normalize.
*)
(* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End Prodtest.

(* ----------------------------------------------------------------- *)
(** *** [let] *)

Module LetTest.

(* let x = pred 6 in succ x *)
Definition test :=
  tlet
    x
    (prd (const 6))
    (scc (var x)).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. (* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  test -->* const 6.
Proof.
(* 
  unfold test. normalize.
*)
(* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End LetTest.

(* ----------------------------------------------------------------- *)
(** *** 和 *)

Module Sumtest1.

(* case (inl Nat 5) of
     inl x => x
   | inr y => y *)

Definition test :=
  tcase (tinl Nat (const 5))
    x (var x)
    y (var y).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. (* 请在此处解答 *) Admitted.

Example reduces :
  test -->* (const 5).
Proof.
(* 
  unfold test. normalize.
*)
(* 请在此处解答 *) Admitted.

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => test0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition test :=
  tlet
    processSum
    (abs x (Sum Nat Nat)
      (tcase (var x)
         n (var n)
         n (test0 (var n) (const 1) (const 0))))
    (pair
      (app (var processSum) (tinl Nat (const 5)))
      (app (var processSum) (tinr Nat (const 5)))).

Example typechecks :
  empty |- test \in (Prod Nat Nat).
Proof. unfold test. eauto 15. (* 请在此处解答 *) Admitted.

Example reduces :
  test -->* (pair (const 5) (const 0)).
Proof.
(* 
  unfold test. normalize.
*)
(* 请在此处解答 *) Admitted.

End Sumtest2.

(* ----------------------------------------------------------------- *)
(** *** 列表 *)

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   lcase l of
     nil => 0
   | x::y => x*x *)

Definition test :=
  tlet l
    (tcons (const 5) (tcons (const 6) (tnil Nat)))
    (tlcase (var l)
       (const 0)
       x y (mlt (var x) (var x))).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 20. (* 请在此处解答 *) Admitted.

Example reduces :
  test -->* (const 25).
Proof.
(* 
  unfold test. normalize.
*)
(* 请在此处解答 *) Admitted.

End ListTest.

(* ----------------------------------------------------------------- *)
(** *** [fix] *)

Module FixTest1.

(* fact := fix
             (\f:nat->nat.
                \a:nat.
                   test a=0 then 1 else a * (f (pred a))) *)
Definition fact :=
  tfix
    (abs f (Arrow Nat Nat)
      (abs a Nat
        (test0
           (var a)
           (const 1)
           (mlt
              (var a)
              (app (var f) (prd (var a))))))).

(** （警告：[fact] 可能通过了类型检查但仍然会有一些类型规则是错误的！） *)

Example typechecks :
  empty |- fact \in (Arrow Nat Nat).
Proof. unfold fact. auto 10. (* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  (app fact (const 4)) -->* (const 24).
Proof.
(* 
  unfold fact. normalize.
*)
(* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End FixTest1.

Module FixTest2.

(* map :=
     \g:nat->nat.
       fix
         (\f:[nat]->[nat].
            \l:[nat].
               case l of
               | [] -> []
               | x::l -> (g x)::(f l)) *)
Definition map :=
  abs g (Arrow Nat Nat)
    (tfix
      (abs f (Arrow (List Nat) (List Nat))
        (abs l (List Nat)
          (tlcase (var l)
            (tnil Nat)
            a l (tcons (app (var g) (var a))
                         (app (var f) (var l))))))).

Example typechecks :
  empty |- map \in
    (Arrow (Arrow Nat Nat)
      (Arrow (List Nat)
        (List Nat))).
Proof. unfold map. auto 10. (* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  app (app map (abs a Nat (scc (var a))))
         (tcons (const 1) (tcons (const 2) (tnil Nat)))
  -->* (tcons (const 2) (tcons (const 3) (tnil Nat))).
Proof.
(* 
  unfold map. normalize.
*)
(* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End FixTest2.

Module FixTest3.

(* equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             test0 m then (test0 n then 1 else 0)
             else test0 n then 0
             else eq (pred m) (pred n))   *)

Definition equal :=
  tfix
    (abs eq (Arrow Nat (Arrow Nat Nat))
      (abs m Nat
        (abs n Nat
          (test0 (var m)
            (test0 (var n) (const 1) (const 0))
            (test0 (var n)
              (const 0)
              (app (app (var eq)
                              (prd (var m)))
                      (prd (var n)))))))).

Example typechecks :
  empty |- equal \in (Arrow Nat (Arrow Nat Nat)).
Proof. unfold equal. auto 10. (* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  (app (app equal (const 4)) (const 4)) -->* (const 1).
Proof.
(* 
  unfold equal. normalize.
*)
(* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

Example reduces2 :
  (app (app equal (const 4)) (const 5)) -->* (const 0).
Proof.
(* 
  unfold equal. normalize.
*)
(* 请在此处解答 *) Admitted.

End FixTest3.

Module FixTest4.

(* let evenodd =
         fix
           (\eo: (Nat->Nat * Nat->Nat).
              let e = \n:Nat. test0 n then 1 else eo.snd (pred n) in
              let o = \n:Nat. test0 n then 0 else eo.fst (pred n) in
              (e,o)) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)
*)

Definition eotest :=
  tlet evenodd
    (tfix
      (abs eo (Prod (Arrow Nat Nat) (Arrow Nat Nat))
        (pair
          (abs n Nat
            (test0 (var n)
              (const 1)
              (app (snd (var eo)) (prd (var n)))))
          (abs n Nat
            (test0 (var n)
              (const 0)
              (app (fst (var eo)) (prd (var n))))))))
  (tlet even (fst (var evenodd))
  (tlet odd (snd (var evenodd))
  (pair
    (app (var even) (const 3))
    (app (var even) (const 4))))).

Example typechecks :
  empty |- eotest \in (Prod Nat Nat).
Proof. unfold eotest. eauto 30. (* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  eotest -->* (pair (const 0) (const 1)).
Proof.
(* 
  unfold eotest. normalize.
*)
(* 请在此处解答 *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End FixTest4.

End Examples.
(** [] *)

(* ================================================================= *)
(** ** 定型的性质 *)

(** 对扩展后的系统证明其可归约性与保型性类似于 STLC，但证明会更长。*)

(* ----------------------------------------------------------------- *)
(** *** 可归约性 *)

(** **** 练习：3 星, standard (STLCE_progress)  

    Complete the proof of [progress].

    Theorem: Suppose empty |- t \in T.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* 给定的类型导出式中的最后规则不可能是
       [T_Var], 因为它不可能是 [empty |- x : T] 这种情形（因为上下文为空）. *)
    inversion H.
  - (* T_Abs *)
    (* 如果规则 [T_Abs] 最后被使用，那么
       [t = abs x T11 t12]，也即一个值。 *)
    left...
  - (* T_App *)
    (* 如果最后被使用的规则是 [T_App]，那么 [t = t1 t2]，
       且有规则的形式我们可以知道
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       由归纳假设，t1 和 2 均要么是值，要么可前进一步。*)
    right.
    destruct IHHt1; subst...
    + (* t1 是值 *)
      destruct IHHt2; subst...
      * (* t2 是值 *)
        (* 如果 [t1] 和 [t2] 同时为值，那么我们可得
           [t1 = abs x T11 t12]，因为抽象是函数类型唯一可能的值。
           但由规则 [ST_AppAbs] 可得
           [(abs x T11 t12) t2 --> [x:=t2]t12]。*)
        inversion H; subst; try solve_by_invert.
        exists (subst x t2 t12)...
      * (* t2 可前进 *)
        (* 如果 [t1] 是值且 [t2 --> t2']，
           那么由 [ST_App2] 可得 [t1 t2 --> t1 t2']。 *)
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    + (* t1 可前进 *)
      (* 最后，如果 [t1 --> t1']，那么由 [ST_App1] 可得 [t1 t2 --> t1' t2]。*)
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  - (* T_Nat *)
    left...
  - (* T_Succ *)
    right.
    destruct IHHt...
    + (* t1 是值 *)
      inversion H; subst; try solve_by_invert.
      exists (const (S n1))...
    + (* t1 可前进 *)
      inversion H as [t1' Hstp].
      exists (scc t1')...
  - (* T_Pred *)
    right.
    destruct IHHt...
    + (* t1 是值 *)
      inversion H; subst; try solve_by_invert.
      exists (const (pred n1))...
    + (* t1 可前进 *)
      inversion H as [t1' Hstp].
      exists (prd t1')...
  - (* T_Mult *)
    right.
    destruct IHHt1...
    + (* t1 是值 *)
      destruct IHHt2...
      * (* t2 是值 *)
        inversion H; subst; try solve_by_invert.
        inversion H0; subst; try solve_by_invert.
        exists (const (mult n1 n0))...
      * (* t2 可前进 *)
        inversion H0 as [t2' Hstp].
        exists (mlt t1 t2')...
    + (* t1 可前进 *)
      inversion H as [t1' Hstp].
      exists (mlt t1' t2)...
  - (* T_Test0 *)
    right.
    destruct IHHt1...
    + (* t1 是值 *)
      inversion H; subst; try solve_by_invert.
      destruct n1 as [|n1'].
      * (* n1=0 *)
        exists t2...
      * (* n1<>0 *)
        exists t3...
    + (* t1 可前进 *)
      inversion H as [t1' H0].
      exists (test0 t1' t2 t3)...
  - (* T_Inl *)
    destruct IHHt...
    + (* t1 可前进 *)
      right. inversion H as [t1' Hstp]...
      (* 存在 (tinl _ t1')... *)
  - (* T_Inr *)
    destruct IHHt...
    + (* t1 可前进 *)
      right. inversion H as [t1' Hstp]...
      (* 存在 (tinr _ t1')... *)
  - (* T_Case *)
    right.
    destruct IHHt1...
    + (* t0 是值 *)
      inversion H; subst; try solve_by_invert.
      * (* t0 是 inl *)
        exists ([x1:=v]t1)...
      * (* t0 是 inr *)
        exists ([x2:=v]t2)...
    + (* t0 可前进 *)
      inversion H as [t0' Hstp].
      exists (tcase t0' x1 t1 x2 t2)...
  - (* T_Nil *)
    left...
  - (* T_Cons *)
    destruct IHHt1...
    + (* 头部（head）是值 *)
      destruct IHHt2...
      * (* 尾部（tail）可前进 *)
        right. inversion H0 as [t2' Hstp].
        exists (tcons t1 t2')...
    + (* 头部可前进 *)
      right. inversion H as [t1' Hstp].
      exists (tcons t1' t2)...
  - (* T_Lcase *)
    right.
    destruct IHHt1...
    + (* t1 是值 *)
      inversion H; subst; try solve_by_invert.
      * (* t1=tnil *)
        exists t2...
      * (* t1=tcons v1 vl *)
        exists ([x2:=vl]([x1:=v1]t3))...
    + (* t1 可前进 *)
      inversion H as [t1' Hstp].
      exists (tlcase t1' t2 x1 x2 t3)...
  - (* T_Unit *)
    left...

  (* Complete the proof. *)

  (* pairs *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)
(* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_progress : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 上下文不变性 *)

(** **** 练习：3 星, standard (STLCE_context_invariance)  

    Complete the definition of [appears_free_in], and the proofs of
   [context_invariance] and [free_in_context]. *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (abs y T11 t12)
  (* 数值 *)
  | afi_succ : forall x t,
     appears_free_in x t ->
     appears_free_in x (scc t)
  | afi_pred : forall x t,
     appears_free_in x t ->
     appears_free_in x (prd t)
  | afi_mult1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (mlt t1 t2)
  | afi_mult2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (mlt t1 t2)
  | afi_test01 : forall x t1 t2 t3,
     appears_free_in x t1 ->
     appears_free_in x (test0 t1 t2 t3)
  | afi_test02 : forall x t1 t2 t3,
     appears_free_in x t2 ->
     appears_free_in x (test0 t1 t2 t3)
  | afi_test03 : forall x t1 t2 t3,
     appears_free_in x t3 ->
     appears_free_in x (test0 t1 t2 t3)
  (* sums *)
  | afi_inl : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinl T t)
  | afi_inr : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinr T t)
  | afi_case0 : forall x t0 x1 t1 x2 t2,
      appears_free_in x t0 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case1 : forall x t0 x1 t1 x2 t2,
      x1 <> x ->
      appears_free_in x t1 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case2 : forall x t0 x1 t1 x2 t2,
      x2 <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  (* 列表 *)
  | afi_cons1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (tcons t1 t2)
  | afi_cons2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (tcons t1 t2)
  | afi_lcase1 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t1 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase2 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t2 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase3 : forall x t1 t2 y1 y2 t3,
     y1 <> x ->
     y2 <> x ->
     appears_free_in x t3 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
(* Increasing the depth of [eauto] allows some more simple cases to
   be dispatched automatically. *)
Proof with eauto 30.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold update, t_update.
    destruct (eqb_stringP x y)...
  - (* T_Case *)
    eapply T_Case...
    + apply IHhas_type2. intros y Hafi.
      unfold update, t_update.
      destruct (eqb_stringP x1 y)...
    + apply IHhas_type3. intros y Hafi.
      unfold update, t_update.
      destruct (eqb_stringP x2 y)...
  - (* T_Lcase *)
    eapply T_Lcase... apply IHhas_type3. intros y Hafi.
    unfold update, t_update.
    destruct (eqb_stringP x1 y)...
    destruct (eqb_stringP x2 y)...

  (* Complete the proof. *)

  (* 请在此处解答 *) Admitted.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
  (* T_Case *)
  - (* left *)
    destruct IHHtyp2 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
  - (* right *)
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
  - (* T_Lcase *)
    clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
    rewrite false_eqb_string in Hctx...

  (* Complete the proof. *)

  (* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_context_invariance : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 替换 *)

(** **** 练习：2 星, standard (STLCE_subst_preserves_typing)  

    Complete the proof of [substitution_preserves_typing]. *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (update Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  (* 定理：如果 [(x|->U ; Gamma) |- t \in S] 且 [empty |- v \in U]，那么
     [Gamma |- [x:=v]t \in S]. *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  (* 证明：对项 [t] 进行归纳。除了 [var] 和 [abs] 外，多数情形可直接从 IH 得证。
     他们不是自动完成的，因为我们需要推理变量之间如何交互。*)
  induction t;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  - (* var *)
    simpl. rename s into y.
    (* 如果 [t = y]，那么通过反演 [update Gamma x U y = Some S]
       我们知道
           [empty |- v \in U] 且
           [(x|->U;Gamma) |- y \in S]。
       我们想要证明 [Gamma |- [x:=v]y \in S]。

       有两个情形需要考虑： [x=y] 或 [x<>y]。 *)
    unfold update, t_update in H1.
    destruct (eqb_stringP x y).
    + (* x=y *)
      (* 如果 [x = y]，那么我们知道 [U = S]，并且
         [[x:=v]y = v]。因此我们必须证明如果
         [empty |- v \in U] 那么 [Gamma |- v \in U]。
         我们已经证明了一个更一般的定理，叫做上下文不变性（context invariance）。*)
      subst.
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
      inversion HT'.
    + (* x<>y *)
    (* 如果 [x <> y]，那么 [Gamma y = Some S] 并且替换不会产生任何影响。
      我们可以通过 [T_Var] 证明 [Gamma |- y \in S]。 *)
      apply T_Var...
  - (* abs *)
    rename s into y. rename t into T11.
    (* 如果 [t = abs y T11 t0]，那么我们知道
         [(x|->U;Gamma) |- abs y T11 t0 \in T11->T12]
         [(y|->T11;x|->U;Gamma) |- t0 \in T12]
         [empty |- v \in U]
       根据归纳假设（IH），我们知道对所有的 [S] 和 [Gamma]，
         若 [(x|->U;Gamma) |- t0 \in S]
         则 [Gamma |- [x:=v]t0 \in S]。

       我们可以计算
         [[x:=v]t = abs y T11 (if eqb_string x y then t0 else [x:=v]t0)]
       且我们必须证明 [Gamma |- [x:=v]t \in T11->T12].  We know
       我们知道可以通过 [T_Abs] 来达到此目的，因此剩下的便是证明：
         [(y|->T11;Gamma) |- if eqb_string x y then t0 else [x:=v]t0
                          \in T12]
       我们考虑两个情形： [x = y] and [x <> y].
    *)
    apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
    (* 如果 [x = y]，那么替换不会产生任何影响。
       上下文不变性展示了 [y:T11;y|->U;Gamma] 和 [y|->T11;Gamma] 是等价的。
       因为前一个上下文展示了 [t0 \in T12]，后者也同样。 *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + (* x<>y *)
      (* 如果 [x <> y]，那么归纳假设和上下文不变性允许我们证明
           [(y|->T11;x|->U;Gamma) |- t0 \in T12]       =>
           [(x|->U;y|->T11;Gamma) |- t0 \in T12]       =>
           [(y|->T11;Gamma) |- [x:=v]t0 \in T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz|Hyz]...
      subst.
      rewrite false_eqb_string...
  - (* tcase *)
    rename s into x1. rename s0 into x2.
    eapply T_Case...
    + (* 左侧 *)
      destruct (eqb_stringP x x1) as [Hxx1|Hxx1].
      * (* x = x1 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_string x1 z)...
      * (* x <> x1 *)
        apply IHt2. eapply context_invariance...
        intros z Hafi.  unfold update, t_update.
        destruct (eqb_stringP x1 z) as [Hx1z|Hx1z]...
        subst. rewrite false_eqb_string...
    + (* 右侧 *)
      destruct (eqb_stringP x x2) as [Hxx2|Hxx2].
      * (* x = x2 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_string x2 z)...
      * (* x <> x2 *)
        apply IHt3. eapply context_invariance...
        intros z Hafi.  unfold update, t_update.
        destruct (eqb_stringP x2 z)...
        subst. rewrite false_eqb_string...
  - (* tlcase *)
    rename s into y1. rename s0 into y2.
    eapply T_Lcase...
    destruct (eqb_stringP x y1).
    + (* x=y1 *)
      simpl.
      eapply context_invariance...
      subst.
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y1 z)...
    + (* x<>y1 *)
      destruct (eqb_stringP x y2).
      * (* x=y2 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP y2 z)...
      * (* x<>y2 *)
        apply IHt3. eapply context_invariance...
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP y1 z)...
        subst. rewrite false_eqb_string...
        destruct (eqb_stringP y2 z)...
        subst. rewrite false_eqb_string...

  (* Complete the proof. *)

  (* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_substitution_preserves_typing : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 保型性 *)

(** **** 练习：3 星, standard (STLCE_preservation)  

    Complete the proof of [preservation]. *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t --> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* 定理：如果 [empty |- t \in T] 且 [t --> t']，那么
     [empty |- t' \in T]. *)
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* 证明：对给定的类型导出式进行归纳。许多情形是矛盾的（[T_Var], [T_Abs]），
     我们只证明有趣的那几个情形。*)
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    (* 如果最后被使用的规则是 [T_App]，那么 [t = t1 t2]，
        且有三个规则会被用于证明 [t --> t']：
       [ST_App1]，[ST_App2]，和 [ST_AppAbs]。
       在前两个情形中，结果可直接从归纳假设中得证。 *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      (* 对于第三个情形，假设
           [t1 = abs x T11 t12]
         且
           [t2 = v2]。
         我们必须证明 [empty |- [x:=v2]t12 \in T2]。
         由假设，我们可得
             [empty |- tabs x T11 t12 \in T1->T2]
         且，由反演可得
             [x:T1 |- t12 \in T2]
         我们已经证明了类型在替换下的不变性，且根据假设可得
             [empty |- v2 \in T1]
         证毕。 *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  (* T_Case *)
  - (* ST_CaseInl *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* ST_CaseInr *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* T_Lcase *)
    + (* ST_LcaseCons *)
      inversion HT1; subst.
      apply substitution_preserves_typing with (List T1)...
      apply substitution_preserves_typing with T1...

  (* Complete the proof. *)

  (* fst and snd *)
  (* 请在此处解答 *)
  (* let *)
  (* 请在此处解答 *)
  (* fix *)
  (* 请在此处解答 *)
(* 请在此处解答 *) Admitted.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_preservation : option (nat*string) := None.
(** [] *)

End STLCExtended.

(* Fri Jul 19 00:33:15 UTC 2019 *)
