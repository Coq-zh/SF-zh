(** * Postscript: 后记 *)

(** 恭喜，课程终于顺利结束了！ *)

(* ################################################################# *)
(** * 回顾一下 *)

(** 到目前为止，我们已经学习了很多内容。我们来快速地回顾一下：

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

(* ################################################################# *)
(** * 继续前行 *)

(** 假如本书的内容引起了你的兴趣，你还可以阅读_'软件基础'_系列的：

           - _'编程语言基础'_（《软件基础》第二卷，与本书作者组类似）
             覆盖了了关于编程语言理论方面的研究生课程，包括霍尔逻辑
             （Hoare logic）、操作语义以及类型系统。

           - _'函数式算法验证'_（《软件基础》第三卷，Andrew Appel 著）
             在使用 Coq 进行程序验证和函数式编程的基础之上，
             讨论了一般数据结构课程中的一系列主题并着眼于其形式化验证。*)

(* ################################################################# *)
(** * 其它资源 *)

(** 进一步学习的资源……

       - 本书包含了一些可选章节，其中讲述的内容或许会对你有用。你可以在
         目录 或
         章节依赖简图 中找到它们。

       - 有关 Coq 的问题，可以查看 Stack Overflow 上的 [#coq] 板块
         (https://stackoverflow.com/questions/tagged/coq)，
         它是个很棒的社区资源。

       - 更多与函数式编程相关的内容：
            - Learn You a Haskell for Great Good, by Miran Lipovaca
              [Lipovaca 2011] (in Bib.v).
              （《Haskell 趣学指南》https://learnyoua.haskell.sg/content/）
            - Real World Haskell, by Bryan O'Sullivan, John Goerzen,
              and Don Stewart [O'Sullivan 2008] (in Bib.v).
              （《Real World Haskell 中文版》http://cnhaskell.com/）
            - ……以及其它关于 Haskell、OCaml、 Scheme、Racket、Scala、F sharp
              等语言的优秀书籍。

       - 更多 Coq 相关的资源：
           - Certified Programming with Dependent Types, by Adam
             Chlipala [Chlipala 2013] (in Bib.v).
           - Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran [Bertot 2004] (in Bib.v).

       - 如果你有兴趣了解现实世界中形式化验证对关键软件的应用，
         可以参阅_'《编程语言基础》'_的后记。

       - 关于使用 Coq 构建形式化验证的系统，可以参考 2017 年 DeepSpec
         夏令营的课程与相关资料。
         https://deepspec.org/event/dsss17/index.html
*)

(* Fri Jul 19 00:32:21 UTC 2019 *)
