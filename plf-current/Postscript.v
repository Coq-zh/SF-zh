(** * Postscript: 后记 *)

(** 恭喜，课程终于顺利结束了！ *)

(* ################################################################# *)
(** * 回顾一下 *)

(** 我们已经学习了很多内容。让我们从_'逻辑基础'_这卷开始快速回顾一下：

   - _'函数式编程'_：
          - “声明式” 编程风格 (在不可变的数据构造上递归，而非在可变的数组或指针结构上循环）
          - 高阶函数
          - 多态 *)

(**
     - _'逻辑'_，软件工程的数学基础：

           逻辑                微积分
        ---------   ~   ------------------
         软件工程          机械工程/土木工程

          - 归纳定义的集合和关系
          - 归纳证明
          - 证明对象 *)

(**
     - _'Coq'_，一个强有力的证明辅助工具
          - 函数式核心语言
          - 核心策略
          - 自动化
*)

(**
     - _'编程语言基础'_

           - 记法和定义技术，用于精确地描述
                - 抽象语法
                - 操作语义
                    - 大步风格
                    - 小步风格
                - 类型系统

           - 程序等价关系

           - 霍尔逻辑

           - 类型系统的基础元理论

              - 可进性与保型性

           - 子类型的理论
*)

(* ################################################################# *)
(** * 环顾周围 *)

(** 在许多进行中的研究项目和现实世界的软件系统中，有很多大规模的应用都使用了
    我们学习的核心内容。为了给读者展示这些技术应用的现状，我们给出一些对软件
    和硬件系统使用形式化和机器检查验证技术的例子。*)

(* ----------------------------------------------------------------- *)
(** *** CompCert 

    _'CompCert'_ 是一个经过了完全形式化验证的 ISO C90 / ANSI C 优化编译器，
    可以为 x86，ARM 和 PowerPC 处理器生成代码。CompCert 完全使用 Gallina
    编写，并使用 Coq 的提取机制生成高效的 OCaml 程序。

    “CompCert 项目研究了如何对至关重要的嵌入式程序的编译器进行形式化验证。
    形式化验证的编译器提供了一个数学化的、机器检查过的证明，用于展示生成的
    可执行代码精确地执行了源程序的语义。通过排除编译器可能引入的缺陷，形式
    化验证的编译器加强了形式化方法所能为源程序提供的保障。”

    2011 年，一项研究使用 CSmith 工具对几个主要的成熟 C 编译器进行了模糊测试
    （fuzz testing），CompCert 也在其中。CSmith 的作者写道：

      - 关于 CompCert 测试结果的惊人事实是其他编译器中端存在的缺陷在 CompCert
        中都不存在。在 2011 年早期，仍在开发中的 CompCert 是我们测试中唯一
        一个 CSmith 找不到错误代码缺陷的编译器。这并不是因为我们不够努力：我们花费了
        六个 CPU-年来做这件事。
        在证明框架中，安全检查是显式的和机器验证过的，而坚若磐石的 CompCert
        强有力地支持了在这样一个证明框架中开发编译器优化会为用户带来切实的好处。

    http://compcert.inria.fr *)

(* ----------------------------------------------------------------- *)
(** *** seL4 

    _'seL4'_ 是一个完全形式化验证的微内核，被认为是世界上第一个对实现的正确性和
    安全保证提供了端对端证明的操作系统内核。它使用 C 和 ARM 汇编实现，并使用
    Isabelle 描述和验证规范。其实现开放了源代码。

    “seL4 已经被全面地形式化验证：我们严谨地从数学上证明了其可执行代码和运行它
    的硬件正确地实现了规范所限定的行为。进一步地，我们证明了规范具有所要求的安全特性
    （完整性和保密性）……验证过程的成本显著少于传统的高可靠性软件开发方式，同时提供了
    传统方式无法比拟的保证。”

    https://sel4.systems. *)

(* ----------------------------------------------------------------- *)
(** *** CertiKOS 

    _'CertiKOS'_ 是一个设计清晰和完全形式化验证的虚拟机器监视器（Hypervisor），
    使用 CompCert C 开发并经过 Coq 验证。

    “CertiKOS 项目的目标是开发一个创新并实用的变成基础设施，用于构建大规模的带证明
    可信系统软件。通过结合近年在程序语言，操作系统和形式化方法领域的进展，我们希望
    回答以下研究问题：（1）什么样的操作系统内核结构可以为可扩展性、安全性和适应性提
    供最佳的支持？（2）何种语义模型和程序逻辑可以表达这些抽象？（3）什么是可信内核
    的合适开发语言和环境？以及（4）如后构建自动化的设施以帮助带证明可信软件开发方式
    真正规模化地应用？”

    http://flint.cs.yale.edu/certikos/ *)

(* ----------------------------------------------------------------- *)
(** *** Ironclad 

    _'Ironclad 应用'_ 是一系列完全形式化验证的 Web 应用，包括一个用于安全地签署
    声明的“公正人”程序，一个密码散列程序，一个多用户的可信计数器，以及一个差分隐私
    数据库。

    系统使用面向验证的程序语言 Dafny 开发，并使用基于霍尔逻辑的工具 Boogie
    验证。

    “Ironclad 应用允许用户安全地将数据传输到远程机器，同时保证远程机器上执行
    的每一条指令都符合描述此应用行为的形式化规范。这不仅仅消除了实现中的的缺陷，
    例如缓冲区溢出、解析错误或数据泄漏，还为用户提供了应用的精确行为。
    我们通过完全的低层次软件验证来确保一点。我们还利用加密技术和安全硬件为形式化验证
    的软件和远程用户之间的通信提供安全通道。”

    https://github.com/Microsoft/Ironclad/tree/master/ironclad-apps *)

(* ----------------------------------------------------------------- *)
(** *** Verdi 

    _'Verdi'_ 是一个用于形式化验证分布式系统的框架。

    “Verdi 支持了从现实化的到理想化的多种故障模型。Verdi 的验证系统变换器
    （Verified System Transformers, VSTs）封装了常见的容错技术。
    开发者可以首先在理想模型下验证一个应用，接着使用 VST 来获得在更恶劣的环境
    中仍然保证了类似性质的应用。Verdi 使用 Coq 证明辅助工具开发，并提取到 OCaml
    程序以供执行。Verdi 系统，包括其容错键值存储系统，相比于其他未验证的类似系统
    具有同等的性能。”

    http://verdi.uwplse.org *)

(* ----------------------------------------------------------------- *)
(** *** DeepSpec 

    _'深度规范的科学（The Science of Deep Specification）'_ 是一项 NSF
    资助的“远征”研究项目（2016 至 2020 年），目标是为软硬件系统提供完整的功能
    正确性规范和验证。项目同时赞助了讲习班和暑期学校。
      - 网站：https://deepspec.org/
      - 概况介绍：
          - https://deepspec.org/about/
          - https://www.youtube.com/watch?v=IPNdsnRWBkk *)

(* ----------------------------------------------------------------- *)
(** *** REMS 

    _'REMS'_ 是一个欧洲项目，关注对主流系统使用严谨的工程方法（Rigorous
    Engineering of Mainstream Systems）。它为广泛使用的重要接口、协议和
    API 提供了精细的形式化规格，这些系统包括 C 语言, ELF 链接器的格式，
    ARM、Power、MIPS、CHERI 和 RISC-V 指令集，ARM 和 Power 处理器的弱内存模型，
    以及 POSIX 文件系统。

    “本项目聚焦于轻量的严谨工程方法：使用精确的规格（事后设计或过程中设计）和对规格的测试，
    以及一些情形下的完全验证。项目强调构建实用的（以及可重用的）语义和工具。我们研究如何为
    一些关键的计算机抽象（处理器架构，程序语言，并发 OS 接口，以及网络协议）构建全面和精确
    的数学模型，以及在新的形式化验证研究，系统研究和程序语言研究中如何重用这些模型。
    为了支持这些，我们也正在开发新的规格工具和理论。”

    https://www.cl.cam.ac.uk/~pes20/rems/ *)

(* ----------------------------------------------------------------- *)
(** *** 其他 *)

(** 其他值得注意的项目还有：
      - Vellvm（LLVM 优化过程的形式化规范和验证）
      - Zach Tatlock 的形式化可信浏览器
      - Tobias Nipkow 对大部分 Java 的形式化工作
      - CakeML 形式化验证的 ML 编译器
      - Greg Morrisett 对 x86 指令集进行的形式化规范，以及 RockSalt
        软件错误分离（Software Fault Isolation）工具（可以称作是一个更快和更安全的
        Google Native Client）
      - Ur/Web 一个用于在 Coq 中嵌入形式化验证的 Web 应用的程序语言
      - Princeton 大学开发的形式化验证软件工具链（Verified Software Toolchain）
*)

(* ################################################################# *)
(** * 继续前行 *)

(** 进一步学习的资源……

       - 本书包含了一些可选章节，其中讲述的内容或许会对你有用。请查看
         目录 和 章节依赖图
         了解更多。

       - 进一步学习霍尔逻辑和程序验证：
            - The Formal Semantics of Programming Languages: An
              Introduction, by Glynn Winskel [Winskel 1993] (in Bib.v).
            - Many practical verification tools, e.g. Microsoft's
              Boogie system, Java Extended Static Checking, etc.

       - 进一步学习编程语言基础：
            - Concrete Semantics with Isabelle/HOL, by Tobias Nipkow
              and Gerwin Klein [Nipkow 2014] (in Bib.v)
            - Types and Programming Languages, by Benjamin C. Pierce
              [Pierce 2002] (in Bib.v).
            - Practical Foundations for Programming Languages, by
              Robert Harper [Harper 2016] (in Bib.v).
            - Foundations for Programming Languages, by John
              C. Mitchell [Mitchell 1996] (in Bib.v).

        - Iron Lambda (http://iron.ouroborus.net/) 是一个 Coq 程序库，
          提供了更多复杂函数式语言的形式化。它填补了本课程和当下的研究论文之间的缺口。
          这个程序库为多种 STLC 和多态 lambda-演算（System F）的变种提供了至少可进性
          和保型性定理。

       - 最后，关于编程语言和形式化验证的学术会议有：
            - Principles of Programming Langauges (POPL)
            - Programming Language Design and Implementation (PLDI)
            - International Conference on Functional Programming (ICFP)
            - Computer Aided Verification (CAV)
            - Interactive Theorem Proving (ITP)
            - Certified Programs and Proofs (CPP)
            - SPLASH/OOPSLA conferences
            - Principles in Practice workshop (PiP)
            - CoqPL workshop
*)

(** $Date$ *)

(* Fri Jul 19 00:33:18 UTC 2019 *)
