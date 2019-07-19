(** * Extraction: 从 Coq 中提取 ML *)

(* ################################################################# *)
(** * 基本的提取方式 *)

(** 对于用 Coq 编写的代码而言，从中提取高效程序的最简方式是十分直白的。

    首先我们需要指定提取的目标语言。可选的语言有三种：提取机制最为成熟的
    OCaml，提取结果大都可以直接使用的 Haskell，以及提取机制有些过时的 Scheme。 *)

Require Coq.extraction.Extraction.
Extraction Language OCaml.

(** 现在我们将待提取的定义加载到 Coq 环境中。你可以直接写出定义，
    也可以从其它模块中加载。 *)

From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import ImpCEvalFun.

(** 最后，我们来指定需要提取的定义，以及用于保存提取结果的文件名。 *)

Extraction "imp1.ml" ceval_step.

(** Coq 在处理此指令时会生成一个名为 [imp1.ml] 的文件，其中包含了提取后的
    [ceval_step] 以及所有递归依赖的文件。编译本章对应的 [.v]
    文件，然后看看生成的 [imp1.ml] 吧！ *)

(* ################################################################# *)
(** * 控制提取特定的类型 *)

(** 我们可以让 Coq 将具体的 [Inductive] 定义提取为特定的 OCaml 类型。
    对于每一个定义，我们都要指明：
      - 该 Coq 类型应当如何用 OCaml 来表示，以及
      - 该类型的构造子应如何转换为目标语言中对应的标识符。 *)

Extract Inductive bool => "bool" [ "true" "false" ].

(** 对于非枚举类型（即构造器接受参数的类型），我们需要给出一个 OCaml
    表达式来作为该类型元素上的“递归器”。（想想丘奇数。）

    （译注：在这一部分，读者可以在为 [nat] 指定对应的类型后使用
    [Extraction plus] 来得到自然数加法的提取结果，以此加深对“递归器”的理解。）*)

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

(** 我们也可以将定义的常量提取为具体的 OCaml 项或者操作符。 *)

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

(** 注意：保证提取结果的合理性是_'你的责任'_。例如，以下指定可能十分自然：

      Extract Constant minus => "( - )".

    但是这样做会引起严重的混乱。（思考一下。为什么会这样呢？）
*)

Extraction "imp2.ml" ceval_step.

(** 检查一下生成的 [imp2.ml] 文件，留意一下此次的提取结果与 [imp1.ml]
    有何不同。 *)

(* ################################################################# *)
(** * 一个完整的示例 *)

(** 为了使用提取的求值器运行 Imp 程序，我们还需要一个小巧的驱动程序
    来调用求值器并输出求值结果。

    为简单起见，我们只取最终状态下前四个存储空间中的内容作为程序的结果。
    （译注：这里的存储空间指作为状态的 [map]。）

    为了更方便地输入例子，我们将会从 [ImpParser] 模块中提取出语法解析器。
    首先需要正确建立 Coq 中的字符串与 OCaml 中字符列表的对应关系。 *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(** 我们还需要翻译另一种布尔值： *)

Extract Inductive sumbool => "bool" ["true" "false"].

(** 提取指令是相同的。 *)

From LF Require Import Imp.
From LF Require Import ImpParser.

From LF Require Import Maps.
Extraction "imp.ml" empty_st ceval_step parse.

(** 现在我们来运行一下生成的 Imp 求值器。首先你应该阅览一下
    [impdriver.ml]（这并非从某个 Coq 源码提取而来，它是手写的。）

    然后用下面的指令将求值器与驱动程序一同编译成可执行文件：

        ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
        ./impdriver

    （编译时所使用的 [-w] 开关只是为了避免输出一些误报的警告信息。） *)

(* ################################################################# *)
(** * 讨论 *)

(** 由于我们证明了 [ceval_step] 函数的行为在适当的意义上与 [ceval]
    关系一致，因此提取出的程序可视作_'已验证的'_ Imp 解释器。
    当然，我们使用的语法分析器并未经过验证，因为我们并未对它进行任何证明！ *)

(* ################################################################# *)
(** * 更进一步 *)

(** 有关提取的更多详情见_'软件基础'_第三卷_'已验证的函数式算法'_中的
    Extract 一章。 *)

(* Fri Jul 19 00:32:21 UTC 2019 *)
