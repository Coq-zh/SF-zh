(** * Stlc: 简单类型 Lambda-演算 *)

(** 简单类型 lambda-演算（simply typed lambda-calculus，STLC）
    作为一种小型演算系统体现了_'函数抽象（functional abstraction）'_这个重要概念，
    函数抽象也以很多种形式（函数，过程，方法等）出现在真实世界的程序语言中。

    在形式化这个演算系统（语法，小步语义和定型规则）及其主要性质（可进性和保型性）时，
    我们采用与上一章相同的流程。新的技术挑战来自于_'变量绑定（variable binding）'_
    和_'替换（substitution）'_。我们将会费一些功夫来处理他们。*)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

(* ################################################################# *)
(** * 简介 *)

(** STLC 构建于一些_'基础类型（base types）'_的集合之上：
    布尔值，数字，字符串等。具体选择哪些基础类型并不重要——语言的构造和它的理论性质
    不会受到影响——因此简单起见，让我们暂时只使用 [Bool]。在本章的最后，我们会看到
    如何添加更多的基础类型，后面的章节我们还会用一些实用的构造，例如序对、记录、子类型
    和可变状态来扩展纯 STLC。

    我们以布尔值常量和条件语句开始，并添加三个构造：
        - 变量
        - 函数抽象
        - 应用

    这给了我们如下的抽象语法构造（先以非形式化的 BNF 记法写下——后面我们
    会形式化它）。 

       t ::= x                         variable
           | \x:T1.t2                  abstraction
           | t1 t2                     application
           | tru                       constant true
           | fls                       constant false
           | test t1 then t2 else t3   conditional
*)

(** 函数抽象 [\x:T.t] 中的 [\] 符号一般写作希腊字母“lambda”（本演算系统由此得名）。
    变量 [x] 叫做函数的_'参数（parameter）'_；项 [t] 是_'函数体（body）'_。
    记号 [:T] 指明了函数可以被应用的参数类型。*)

(** 一些例子：

      - [\x:Bool. x]

        布尔值的恒等函数。

      - [(\x:Bool. x) tru]

        被应用于 [tru] 的布尔值恒等函数。

      - [\x:Bool. test x then fls else tru]

        布尔值的“否定”函数。

      - [\x:Bool. tru]

        总是接受（布尔值）参数并返回 [tru] 的常量函数。
      - [\x:Bool. \y:Bool. x]

        接受两个布尔值做参数，并返回第一个参数的函数。（在 Coq 中，二元函数
        其实就是一个一元函数，只是其函数体也是一元函数。）

      - [(\x:Bool. \y:Bool. x) fls tru]

        一个接受两个布尔值做参数，并返回第一个参数的函数，接着它被应用于两个布尔值参数
        [fls] 和 [tru]。

        在 Coq 中，应用是左结合的——也即，这个表达式被解析为
        [((\x:Bool. \y:Bool. x) fls) tru]。

      - [\f:Bool->Bool. f (f tru)]

        一个高阶函数其接受一个函数 [f]（从布尔值到布尔值）作为参数，并应用
        [f] 于参数 [tru]；其结果又被应用于 [f]。

      - [(\f:Bool->Bool. f (f tru)) (\x:Bool. fls)]

        同一个高阶函数，被应用于返回 [fls] 的常函数。 *)

(** 正如最后几个例子中展示的那样，STLC是一个支持_'高阶（higher-order）'_
    函数的语言：我们可以写出接受其他函数作为参数，或返回其他函数作为结果的函数。

    但是 STLC 并没提供任何原生语法来定义_'有名函数（named functions）'_——
    所有的函数都是“匿名的（anonymous）”。我们会在 [MoreStlc] 一章中看到添加有名
    函数是十分简单的——确实，基本的命名和绑定机制其实是同一回事。

    STLC 的_'类型（types）'_包括 [Bool]，其用于把 [tru] 和 [fls] 这些常量
    和其他产生布尔值的复杂计算归为一类；还有_'函数类型（arrow types）'_，用于把函
    数归为一类。

      T ::= Bool
          | T -> T

    比如说：

      - [\x:Bool. fls] 有类型 [Bool->Bool]

      - [\x:Bool. x] 有类型 [Bool->Bool]

      - [(\x:Bool. x) tru] 有类型 [Bool]

      - [\x:Bool. \y:Bool. x] 有类型 [Bool->Bool->Bool]
                              （即 [Bool -> (Bool->Bool）]）

      - [(\x:Bool. \y:Bool. x) fls] 有类型 [Bool->Bool]

      - [(\x:Bool. \y:Bool. x) fls tru] 有类型 [Bool] *)

(* ################################################################# *)
(** * 语法 *)

(** 我们接下来形式化 STLC 的语法。 *)

Module STLC.

(* ================================================================= *)
(** ** 类型 *)

Inductive ty : Type :=
  | Bool  : ty
  | Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** 项 *)

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

(** 请注意一个形如 [\x:T.t] 的抽象（形式化地讲是 [abs x T t]）包含其参数
    [T] 的类型注释，相反在 Coq（以及其他函数式语言，比如 ML，Haskell等）中，
    会使用类型推导来填补这些类型注释。我们在此不考虑类型推导。 *)

(** 一些例子…… *)

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (abs x Bool (var x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (abs x (Arrow (Arrow Bool Bool)
                      (Arrow Bool Bool))
    (var x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (abs x Bool (abs y Bool (var x))).

(** [notB = \x:Bool. test x then fls else tru] *)

Notation notB := (abs x Bool (test (var x) fls tru)).

(** （我们使用 [Notation] 而非 [Definition] 使 [atuo] 更有效。）*)

(* ################################################################# *)
(** * 操作语义 *)

(** 为了定义 STLC 项的小步语义，我们以值的集合的定义开始。接着，我们定义两个
    重要的概念，_'自由变量（free variables）'_和_'替换（substitution）'_，
    他们在函数应用的归约规则中会被用到。最后，我们给出小步归约关系。 *)

(* ================================================================= *)
(** ** 值 *)

(** 在定义 STLC 的值时，我们有几个情形需要考虑。

    首先，对于布尔值而言是显然的：[true] 和 [false] 是仅有的值。
    一个 [test] 表达式不是值。*)

(** 其次，一个应用也不会是值：它表示一个函数正在某个参数上被调用，显然还可以继续归约。*)

(** 第三，对于抽象，我们有几个选择：

      - 我们可以说仅当 [t] 是值时 [\x:T. t] 是值——也即，仅当函数体已经被归约
        （在不知道被应用的参数是什么的情况下尽可能地归约）。

      - 或者，我们可以说不论 [t] 是不是值，[\x:T. t] 都是一个值——换句话说，
        归约止于抽象。

    在 Coq 中表达式通常是以第一种方式求值的——比如说，

         Compute (fun x:bool => 3 + 4)

    会得到

          fun x:bool => 7

    多数现实世界中的程序语言选择了第二种方式——函数体的归约仅发生在函数实际被应用
    于某个参数时。在这里我们也选择第二种方式。*)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.

Hint Constructors value.

(** 最后，我们必须考虑什么构成了一个_'完整（complete）'_的程序。

    直观地讲，一个“完整的程序”不能包含未定义的变量。我们很快会看到如何定义 STLC
    项中的_'自由（free）'_变量。一个完整的程序是_'闭合的（closed）'_——也就是说，
    它不含有自由变量。

    （相反，含有自由变量的项一般被叫做_'开放项（open term）'_。） *)

(** 由于我们决定不对抽象内的表达式进行归约，因此也不必担心变量是否是值这个问题。
    因为我们总是“从外向内”地归约程序，这意味着 [step] 关系仅会处理闭合项。 *)

(* ================================================================= *)
(** ** 替换 *)

(** 现在我们来到了 STLC 的核心：用一个项替换另一个项中的变量。这个操作在下面用于
    定义函数应用的操作语义，其中我们会需要用一个参数项替换函数体中出现的形式参数。
    比如说，我们会归约

       (\x:Bool. test x then tru else x) fls

    到

       test fls then tru else fls

    这步归约将函数体中出现的参数 [x] 替换为 [fls]。

    一般来说，我们可以用给定的项 [s] 替换的某另一个项 [t] 中出现个变量 [x]。
    在非形式化的讨论中，这通常被写做 [ [x:=s]t ]，并读做“替换 [t] 中的 [x]
    为 [s]”。*)

(** 这里有一些例子：

      - [[x:=tru] (test x then x else fls)]
           产生 [test tru then tru else fls]

      - [[x:=tru] x] 产生 [tru]

      - [[x:=tru] (test x then x else y)] 产生 [test tru then tru else y]

      - [[x:=tru] y] 产生 [y]

      - [[x:=tru] fls] yields [fls] (vacuous substitution)

      - [[x:=tru] (\y:Bool. test y then x else fls)]
           产生 [\y:Bool. test y then tru else fls]

      - [[x:=tru] (\y:Bool. x)] 产生 [\y:Bool. tru]

      - [[x:=tru] (\y:Bool. y)] 产生 [\y:Bool. y]

      - [[x:=tru] (\x:Bool. x)] 产生 [\x:Bool. x]

    最后一个例子非常重要：替换 [\x:Bool. x] 中的 [x] 为 [tru] _'不'_会产生
    [\x:Bool. tru]！因为 [\x:Bool. x] 中的 [x] 是被这个抽象所_'绑定的（bound）'_：
    它是一个新的、局部的名字，只是恰巧写做了跟某个全局名字一样的 [x]。*)

(** 这是非形式化的定义……

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T11. t12)   = \x:T11. t12
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12     if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]tru             = tru
       [x:=s]fls             = fls
       [x:=s](test t1 then t2 else t3) =
              test [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)

(** ……以及形式化的： *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(** _'技术注解'_：如果我们考虑用于替换掉某个变量的项 [s] 其本身也含有自由变量，
    那么定义替换将会变得困难一点。由于我们仅对定义在_'闭合'_项（也即像 [\x:Bool. x]
    这种绑定了内部全部变量的项）上的 [step] 关系有兴趣，我们可以规避这个额外的复杂性，
    但是当形式化构造更丰富的语言时，我们必须考虑这一点。*)

(** 比如说，使用上面的替换定义将 [t = \r:Bool. z]（其中 [r] 为绑定变量）中的
    [z] 替换为_'开放'_项 [s = \x:Bool. r]（其中 [r] 是引用了某个全局资源的自由变量），
    我们会得到 [\r:Bool. \x:Bool. r]。这时，[s] 中的自由引用 [r] 被 [t] 所引入
    的绑定所“捕获”。

    为什么这是件坏事呢？因为它违反了“绑定变量的名字不应当改变语义”这个原则。打个比方，
    如果把 [t] 的绑定变量重命名，比如说，[t' = \w:Bool. z]，那么 [[z:=s]t']
    会产生 [\w:Bool. \x:Bool. r]，其行为和 [[z:=s]t = \r:Bool. \x:Bool. r]
    并不相同。这意味着，重命名绑定变量改变了 [t] 在替换时的行为。 *)

(** 对于这个问题，更详细的讨论可参考 [Aydemir 2008] (in Bib.v)。*)

(** **** 练习：3 星, standard (substi_correct)  

    上面我们使用了 Coq 的 [Fixpoint] 功能将替换定义为一个_'函数'_。
    假设，现在我们想要将替换定义为一个归纳的_'关系'_ [substi]。作为开始，我们给出了
    [Inductive] 定义的头部和其中一个构造子；你的任务是完成剩下的构造子，并证明
    你的定义同替换函数的定义相一致。 *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  (* 请在此处解答 *)
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 归约 *)

(** STLC 的小步语义与之前学过的小步语义遵循了同样的模式。直观地说，
    对于函数应用我们首先归约其左手边的项（也即函数）直到其成为一个抽象；
    接着归约其右手边的项（也即参数）直到其成为一个值；最后我们用参数替换函数
    体内的绑定变量。最后一条规则可以非形式化地写做

      (\x:T.t12) v2 --> [x:=v2]t12

    传统上这也被称作_'beta-归约（beta-reduction）'_ *)

(** 
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 --> [x:=v2]t12

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

    ……还有对条件语句的规则：

                    --------------------------------               (ST_TestTru)
                    (test tru then t1 else t2) --> t1

                    ---------------------------------              (ST_TestFls)
                    (test fls then t1 else t2) --> t2

                             t1 --> t1'
      --------------------------------------------------------     (ST_Test)
      (test t1 then t2 else t3) --> (test t1' then t2 else t3)
*)

(** 形式化的： *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1  t2'
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* ================================================================= *)
(** ** 例子 *)

(** 例子：

      (\x:Bool->Bool. x) (\x:Bool. x) -->* \x:Bool. x

    即

      idBB idB -->* idB
*)

Lemma step_example1 :
  (app idBB idB) -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

(** 例子：

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            -->* \x:Bool. x

    即

      (idBB (idBB idB)) -->* idB.
*)

Lemma step_example2 :
  (app idBB (app idBB idB)) -->* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

(** 例子：

      (\x:Bool->Bool. x)
         (\x:Bool. test x then fls else tru)
         tru
            -->* fls

    即

       (idBB notB) tru -->* fls.
*)

Lemma step_example3 :
  app (app idBB notB) tru -->* fls.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_TestTru. apply multi_refl.  Qed.

(** 例子：

      (\x:Bool -> Bool. x)
         ((\x:Bool. test x then fls else tru) tru)
            -->* fls

    即

      idBB (notB tru) -->* fls.

    （请注意，虽然这个项并不会通过类型检查，我们还是可以看看它是如何归约的。）
*)

Lemma step_example4 :
  app idBB (app notB tru) -->* fls.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_TestTru.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

(** 我们可以使用 [Smallstep] 一章中定义的 [normalize] 策略来简化这些证明。 *)

Lemma step_example1' :
  app idBB idB -->* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  app idBB (app idBB idB) -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  app (app idBB notB) tru -->* fls.
Proof. normalize.  Qed.

Lemma step_example4' :
  app idBB (app notB tru) -->* fls.
Proof. normalize.  Qed.

(** **** 练习：2 星, standard (step_example5)  

    请分别使用和不使用 [normalize] 证明以下命题。 *)

Lemma step_example5 :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma step_example5_with_normalize :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 定型 *)

(** 接下来我们考虑 STLC 的类型关系。 *)

(* ================================================================= *)
(** ** 上下文 *)

(** _'问'_：项 "[x y]" 的类型是什么？

    _'答'_：这取决于 [x] 和 [y] 的类型是什么！

    也就是说，为了给一个项指派类型，我们需要知道关于其中自由变量的类型的假设。

    这把我们引向了一个三元_'类型断言（type judgement）'_，非形式化地写做 [Gamma |- t \in T]，
    其中 [Gamma] 是一个“类型上下文（typing context）”——一个变量到他们的
    类型的映射。 *)

(** 使用通常偏映射的记号，我们用 [(X |-> T11, Gamma)] 来表示“更新偏函数 [Gamma]
    使其也将 [x] 映射到 [T]”。*)

Definition context := partial_map ty.

(* ================================================================= *)
(** ** 类型关系 *)

(** 
                              Gamma x = T
                            ----------------                            (T_Var)
                            Gamma |- x \in T

                   (x |-> T11 ; Gamma) |- t12 \in T12
                   ----------------------------------                   (T_Abs)
                    Gamma |- \x:T11.t12 \in T11->T12

                        Gamma |- t1 \in T11->T12
                          Gamma |- t2 \in T11
                         ----------------------                         (T_App)
                         Gamma |- t1 t2 \in T12

                         ---------------------                          (T_Tru)
                         Gamma |- tru \in Bool

                         ---------------------                          (T_Fls)
                         Gamma |- fls \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T
       --------------------------------------------------------------   (T_Test)
                  Gamma |- test t1 then t2 else t3 \in T

    我们可以把形如 [Gamma |- t \in T] 的三元关系读做：
    “在假设 Gamma 下，项 [t] 有类型 [T]。” *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in Arrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- app t1 t2 \in T12
  | T_Tru : forall Gamma,
       Gamma |- tru \in Bool
  | T_Fls : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(** ** 例子 *)

Example typing_example_1 :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** 请注意，由于我们在提示数据库中添加了 [has_type] 构造子，因此 [auto]
    将可以直接解决这个证明。*)

Example typing_example_1' :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. auto.  Qed.

(** 更多例子：

       empty |- \x:A. \y:A->A. y (y x)
             \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof with auto using update_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** 练习：2 星, standard, optional (typing_example_2_full)  

    请在不使用 [auto]，[eauto]，[eapply]（或者 [...]）的情况下证明同一个命题： *)

Example typing_example_2_full :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (typing_example_3)  

    请形式化地证明以下类型导出式成立：

    
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             \in T.
*)

Example typing_example_3 :
  exists T,
    empty |-
      (abs x (Arrow Bool Bool)
         (abs y (Arrow Bool Bool)
            (abs z Bool
               (app (var y) (app (var x) (var z)))))) \in
      T.
Proof with auto.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 我们也可以证明某些项_'不'_可定型。比如说，我们可以形式化地检查对于
    [\x:Bool. \y:Bool, x y] 来说没有类型导出式为其定型——也即，

    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y \in T.
*)

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (abs x Bool
            (abs y Bool
               (app (var x) (var y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.  Qed.

(** **** 练习：3 星, standard, optional (typing_nonexample_3)  

    另一个例子：

    ~ (exists S T,
          empty |- \x:S. x x \in T).
*)

Example typing_nonexample_3 :
  ~ (exists S T,
        empty |-
          (abs x S
             (app (var x) (var x))) \in
          T).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

End STLC.

(* Fri Jul 19 00:33:15 UTC 2019 *)
