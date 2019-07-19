(** * Lists: 使用结构化的数据 *)

From LF Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * 数值序对 *)

(** 在 [Inductive] 类型定义中，每个构造子（Constructor）可以有任意多个参数
    —— 可以没有（如 [true] 和 [O]），可以只有一个（如 [S]），也可以更多
    （如 [nybble]，以及下文所示）： *)

Inductive natprod : Type :=
| pair (n1 n2 : nat).

(** 此声明可以读作：“只有一种方式来构造一个数值序对：通过将构造子 [pair]
    应用到两个 [nat] 类型的参数上”。 *)

Check (pair 3 5).

(** 下述函数分别用于提取二元组中的第一个和第二个分量。 *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** 鉴于二元组较为常用，不妨以标准的数学记法 [(x,y)] 取代 [pair x y]。
    通过 [Notation] 向 Coq 声明该记法： *)

Notation "( x , y )" := (pair x y).

(** The new pair notation can be used both in expressions and in
    pattern matches. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Note that pattern-matching on a pair (with parentheses: [(x, y)])
    is not to be confused with the "multiple pattern" syntax
    (with no parentheses: [x, y]) that we have seen previously.

    The above examples illustrate pattern matching on a pair with
    elements [x] and [y], whereas [minus] below (taken from
    [Basics]) performs pattern matching on the values [n]
    and [m].

       Fixpoint minus (n m : nat) : nat :=
         match n, m with
         | O   , _    => O
         | S _ , O    => n
         | S n', S m' => minus n' m'
         end.

    The distinction is minor, but it is worth knowing that they
    are not the same. For instance, the following definitions are
    ill-formed:

        (* Can't match on a pair with multiple patterns: *)
        Definition bad_fst (p : natprod) : nat :=
          match p with
          | x, y => x
          end.

        (* Can't match on multiple values with pair patterns: *)
        Definition bad_minus (n m : nat) : nat :=
          match n, m with
          | (O   , _   ) => O
          | (S _ , O   ) => n
          | (S n', S m') => bad_minus n' m'
          end.
*)

(** 我们现在来证明一些有关二元组的简单事实。

    定理倘若以稍显古怪的方式书写，则只需 [reflexivity]（及其内建的简化）
    即可完成证明。 *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** 但是，如果我们用一种更为自然的方式来陈述此引理的话，只用
    [reflexivity] 还不够。 *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* 啥也没有归约！ *)
Abort.

(** 我们必须要向 Coq 展示 [p] 的具体结构，这样 [simpl] 才能对
    [fst] 和 [snd] 做模式匹配。通过 [destruct] 可以达到这个目的。 *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** 注意：不同于解构自然数产生两个子目标，[destruct] 在此只产生
    一个子目标。这是因为 [natprod] 只有一种构造方法。 *)

(** **** 练习：1 星, standard (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 数值列表 *)

(** 通过推广序对的定义，数值_'列表'_类型可以这样描述：
    “一个列表要么是空的，要么就是由一个数和另一个列表组成的序对。” *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(** 例如，这是一个三元素列表： *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** 和序对一样，使用熟悉的编程记法来表示列表会更方便些。
    以下两个声明能让我们用 [::] 作为中缀的 [cons] 操作符，
    用方括号作为构造列表的“外围（outfix）”记法。 *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** 我们不必完全理解这些声明，但如果你感兴趣的话，我会大致说明一下
    发生了什么。 [right associativity] 告诉 Coq 当遇到多个 [::]
    时如何给表达式加括号，如此一来下面三个声明做的就是同一件事： *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** [at level 60] 告诉 Coq 当遇到表达式和其它中缀运算符时应该如何加括号。
    例如，我们已经为 [plus] 函数定义了 [+] 中缀符号，它的优先级是 50：

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

    [+] 会比 [::] 结合的更紧密，所以 [1 + 2 :: [3]] 会被解析成
    [(1 + 2) :: [3]] 而非 [1 + (2 :: [3])]。

   (当你在 [.v] 文件中看到“[1 + (2 :: [3])]”这样的记法时可能会很疑惑。
   最里面那个括住了 3 的方括号，标明了它是一个列表。而外层的方括号则是用来指示
   “coqdoc”这部分要被显示为代码而非普通的文本；在生成的 HTML
   文件中，外层的方括号是看不到的。)

   上面的第二和第三个 [Notation] 声明引入了标准的方括号记法来表示列表；
   第三个声明的右半部分展示了在 Coq 中声明 n 元记法的语法，
   以及将它们翻译成嵌套的二元构造子序列的方法。 *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(** 有很多函数可以方便地操作列表。例如 [repeat] 函数接受一个数字
    [n] 和一个 [count]，返回一个长度为 [count]，每个元素都是 [n] 的列表。 *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

(** [length] 函数用来计算列表的长度。 *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** [app] 函数用来把两个列表联接起来。 *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** 鉴于下文中 [app] 随处可见，不妨将其定义为中缀运算符。 *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Head（带默认值）与 Tail *)

(** 下面介绍列表上的两种运算：[hd] 函数返回列表的第一个元素（即“表头”）；
    [tl] 函数返回列表除去第一个元素以外的部分（即“表尾”）。考虑到空表没有表头，
    传入一个参数作为返回的默认值。 *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** 练习 *)

(** **** 练习：2 星, standard, recommended (list_funs)  

    完成以下 [nonzeros]、[oddmembers] 和 [countoddmembers] 的定义，
    你可以查看测试函数来理解这些函数应该做什么。 *)

Fixpoint nonzeros (l:natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* 请在此处解答 *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* 请在此处解答 *) Admitted.

Definition countoddmembers (l:natlist) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* 请在此处解答 *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* 请在此处解答 *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, advanced (alternate)  

    完成 [alternate] 的定义，它从两个列表中交替地取出元素并合并为一个列表，
    就像把拉链“拉”起来一样。更多具体示例见后面的测试。

    （注意：[alternate] 有一种自然而优雅的定义，但是这一定义无法满足 Coq
    对于 [Fixpoint] 必须“显然会终止”的要求。如果你发现你被这种解法束缚住了，
    可以试着换一种稍微啰嗦一点的解法，比如同时对两个列表中的元素进行操作。
    有种可行的解法需要定义新的序对，但这并不是唯一的方法。） *)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* 请在此处解答 *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* 请在此处解答 *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* 请在此处解答 *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 用列表实现口袋（Bag） *)

(** [bag]（或者叫 [multiset] 多重集）类似于集合，只是其中每个元素都能出现不止一次。
   口袋的一种可行的表示是列表。 *)

Definition bag := natlist.

(** **** 练习：3 星, standard, recommended (bag_functions)  

    为袋子完成以下 [count]、[sum]、[add]、和 [member] 函数的定义。 *)

Fixpoint count (v:nat) (s:bag) : nat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** 这些命题都能通过 [reflexivity] 来证明。 *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* 请在此处解答 *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* 请在此处解答 *) Admitted.

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum : bag -> bag -> bag
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* 请在此处解答 *) Admitted.

Definition add (v:nat) (s:bag) : bag
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* 请在此处解答 *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* 请在此处解答 *) Admitted.

Definition member (v:nat) (s:bag) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* 请在此处解答 *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (bag_more_functions)  

    你可以把下面这些和 [bag] 有关的函数当作额外的练习 *)

(** 倘若某口袋不包含所要移除的数字，那么将 [remove_one] 作用其上不应改变其内容。
    （本练习为选做，但高级班的学生为了完成后面的练习，需要写出 [remove_one]
    的定义。） *)

Fixpoint remove_one (v:nat) (s:bag) : bag
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* 请在此处解答 *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* 请在此处解答 *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* 请在此处解答 *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* 请在此处解答 *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* 请在此处解答 *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* 请在此处解答 *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* 请在此处解答 *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* 请在此处解答 *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* 请在此处解答 *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, recommended (bag_theorem)  

    写一个你认为有趣的关于袋子的定理 [bag_theorem]，然后证明它；
    这个定理需要用到 [count] 和 [add]。注意，这是个开放性问题。
    也许你写下的定理是正确的，但它可能会涉及到你尚未学过的技巧因而无法证明。
    如果你遇到麻烦了，欢迎提问！ *)

(*
Theorem bag_theorem : ...
Proof.
  ...
Qed.
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_bag_theorem : option (nat*string) := None.
(* Note to instructors: For silly technical reasons, in this
   file (only) you will need to write [Some (Datatypes.pair 3 ""%string)]
   rather than [Some (3,""%string)] to enter your grade and comments. 

    [] *)

(* ################################################################# *)
(** * 有关列表的论证 *)

(** 和数字一样，有些列表处理函数的简单事实仅通过化简就能证明。
    例如，对于下面这个例子，[reflexivity] 所做的简化就已经足够了... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ...由于 [[]] 被替换进了 [app] 定义中相应的“被检”分支
    （即经由匹配“仔细检查”过值的表达式），整个匹配得以被简化。 *)

(** 和数字一样，有时对一个列表做分类讨论（是否是空）是非常有用的。 *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** 在这里 [nil] 的情况能够工作是因为我们定义了 [tl nil = nil]，
    而 [destruct] 策略中 [as] 注解引入的两个名字，[n] 和 [l']，分别对应了
    [cons] 构造子的两个参数（正在构造的列表的头和尾）。 *)

 (** 然而一般来说，许多关于列表的有趣定理都需要用到归纳法来证明。 *)

(* ================================================================= *)
(** ** 一点点说教 *)

(** 只是阅读证明的话，你不会获得什么特别有用的东西。搞清楚每一个细节非常重要，
    你应该在 Coq 中单步执行这些证明并思考每一步在整个证明中的作用，否则练习题将毫无用处。
    啰嗦完毕。 *)

(* ================================================================= *)
(** ** 对列表进行归纳 *)

(** 比起对自然数的归纳，读者可能对归纳证明 [natlist] 这样的数据类型更加陌生。
    不过基本思路同样简单。每个 [Inductive] 声明定义了一组数据值，
    这些值可以用声明过的构造子来构造：布尔值可以用 [true] 或 [false] 来构造；
    自然数可以用 [O] 或 [S] 应用到另一个自然数上来构造；而列表可以用 [nil]
    或者将 [cons] 应用到一个自然数和另一个列表上来构造。

    除此以外，归纳定义的集合中元素的形式 _'只能是'_ 构造子对其它项的应用；
    这一事实同时也给出了一种对归纳定义的集合进行论证的方法：一个自然数要么是
    [O]，要么就是 [S] 应用到某个_'更小'_的自然数上；一个列表要么是 [nil]，
    要么就是 [cons] 应用到某个数字和某个_'更小'_的列表上，诸如此类。
    所以，如果我们有某个命题 [P] 涉及列表 [l]，而我们想证明 [P] 对 _'一切'_
    列表都成立，那么可以像这样推理：

    - 首先，证明当 [l] 为 [nil] 时 [P l] 成立。

    - 然后，证明当 [l] 为 [cons n l'] 时 [P l] 成立，其中 [n] 是某个自然数，[l']
      是某个更小的列表，假设 [P l'] 成立.

    由于较大的列表只能通过较小的列表构造出来，最终这个较小的列表会变成
    [nil]，这两点合在一起就完成了 [P] 对一切列表 [l] 成立的证明。下面是个具体的例子： *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** 注意，和归纳自然数时一样，此处 [induction] 策略的 [as...] 从句为在
    “[l1] 由构造子 [cons] 构造而来”这一情况时出现的“更小的列表”和归纳假设取了名字。
    再次强调，如果你把 Coq 的证明当做静态的文档，那么可能不会有特别多的收获 ——
    如果你通过交互式的 Coq 会话来阅读证明，就能看到当前的目标和上下文，
    而这些状态在你阅读写下来的脚本时是不可见的。所以一份用自然语言写成的证明 ——
    写给人看的 —— 需要包含更多的提示来帮助读者理解当前的状态，
    比如第二种情况下的归纳假设到底是什么。 *)

(** _'定理'_：对所有的列表 [l1], [l2], 和 [l3]，
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)]。

   _'证明'_: 通过对 [l1] 使用归纳法。

   - 首先, 假设 [l1 = []]。我们必须证明：

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     这可以通过展开 [++] 的定义得到。

   - 然后, 假设 [l1 = n::l1']，有：

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     （归纳假设）。我们必须证明：

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     根据 [++] 的定义, 上式等价于：

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     该式可通过我们的归纳假设立即证得。  [] *)

(* ----------------------------------------------------------------- *)
(** *** 反转列表 *)

(** 举一个更加深入的例子来说明对列表的归纳证明：假设我们使用 [app]
    来定义一个列表反转函数 [rev]： *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** [rev] 的性质 *)

(** Now, for something a bit more challenging than the proofs
    we've seen so far, let's prove that reversing a list does not
    change its length.  Our first attempt gets stuck in the successor
    case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* 这种情况比较棘手。我们从一般的化简开始。 *)
    simpl.
    (* 现在我们好像卡住了：目标是要证明涉及 [++] 的等式，
       但是我们在上下文和全局环境下并没有任何有用的等式！
       通过用 IH 来重写目标，我们可以推进一点... *)
    rewrite <- IHl'.
    (* ...但也仅此而已。 *)
Abort.

(** 不妨单独提出引理，阐述 [++] 与 [length] 形成的等式关系，
    以推进证明。 *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* 课上已完成 *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** 注意，为了让该引理尽可能 _'通用'_，我们不仅关心由 [rev] 得到的列表，
    还要对 _'所有'_ 的 [natlist] 进行全称量化。这很自然，因为这个证明目标
    显然不依赖于被反转的列表。除此之外，证明这个更普遍的性质也更容易些。 *)

(** 现在我们可以完成最初的证明了。 *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.  Qed.

(** 作为对比，以下是这两个定理的非形式化证明：

    _'定理'_：对于所有的列表 [l1] 和 [l2]，
       [length (l1 ++ l2) = length l1 + length l2].

    _'证明'_：对 [l1] 进行归纳。

    - 首先，假设 [l1 = []]。我们必须证明

        length ([] ++ l2) = length [] + length l2,

      根据 [length] 和 [++] 的定义，上式显然可得。

    - 其次，假设 [l1 = n::l1']，并且

        length (l1' ++ l2) = length l1' + length l2.

      我们必须证明

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      根据 [length] 和 [++] 的定义以及归纳假设，上式显然可得。 [] *)

(** _'定理'_: 对于所有的列表 [l]，[length (rev l) = length l]。

    _'证明'_: 对 [l] 进行归纳。

      - 首先，假设 [l = []]。我们必须证明

          length (rev []) = length [],

        根据 [length] 和 [rev] 的定义，上式显然可得。

      - 其次，假设 [l = n::l']，并且

          length (rev l') = length l'.

        我们必须证明

          length (rev (n :: l')) = length (n :: l').

        根据 [rev] 的定义，上式来自于

          length ((rev l') ++ [n]) = S (length l')

        根据之前的引理，此式等同于

          length (rev l') + length [n] = S (length l').

        根据归纳假设和 [length] 的定义，上式显然可得。 [] *)

(** 这些证明的风格实在是冗长而迂腐。几次练习之后，我们会发现减少细枝末节，
    详述不太显然的步骤更有助于我们理解证明。毕竟细节更容易在大脑中思考，
    必要时我们还可以在草稿纸上补全。下面我们以一种更加紧凑的方式呈现之前的证明： *)

(** _'定理'_：
     对于所有 [l]，[length (rev l) = length l]。

    _'证明'_：首先，观察到 [length (l ++ [n]) = S (length l)] 对一切 [l] 成立
    （通过对 [l] 的归纳直接可得）。当 [l = n'::l'] 时，通过再次对 [l] 使用归纳，
    然后同时使用之前观察得到的性质和归纳假设即可证明。 [] *)

(** 一般而言，在不同的情况下合适的风格也会不同：读者对这个问题了解程度，
    以及当前的证明与读者熟悉的证明之间的相似度都会影响到这一点。
    对于我们现在的目的而言，最好先用更加冗长的方式。 *)

(** ** [Search] 搜索*)

(** 我们已经见过很多需要使用之前证明过的结论（例如通过 [rewrite]）来证明的定理了。
    但是在引用别的定理时，我们必须事先知道它们的名字。当然，即使是已被证明的定理本身
    我们都不能全部记住，更不用提它们的名字了。

    Coq 的 [Search] 指令在这时就非常有用了。执行 [Search foo] 会让 Coq
    显示所有涉及到 [foo] 的定理。例如，去掉下面的注释后，
    你会看到一个我们证明过的所有关于 [rev] 的定理的列表： *)

(*  Search rev. *)

(** 在接下来的学习中，你要记得使用 [Search]，它能为你节约大量的时间！

    如果你正在使用 ProofGeneral，那么可以用 [C-c C-a C-a] 来运行 [Search]。
    通过 [C-c C-;] 可以将它返回的结果粘贴到缓冲区内。 *)

(* ================================================================= *)
(** ** 列表练习，第一部分 *)

(** **** 练习：3 星, standard (list_exercises)  

    更多有关列表的实践： *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* 请在此处解答 *) Admitted.

(** 下面的练习有简短的解法，如果你开始发现情况已经复杂到你无法理清的程度，
    请后退一步并试着寻找更为简单的方法。 *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* 请在此处解答 *) Admitted.

(** 一个关于你对 [nonzeros] 的实现的练习： *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (eqblist)  

    填写 [eqblist] 的定义，它通过比较列表中的数字来判断是否相等。
    证明对于所有列表 [l]，[eqblist l l] 返回 [true]。 *)

Fixpoint eqblist (l1 l2 : natlist) : bool
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
 (* 请在此处解答 *) Admitted.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
(* 请在此处解答 *) Admitted.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
 (* 请在此处解答 *) Admitted.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 列表练习, 第二部分 *)

(** 下面这组简单的定理用于证明你之前关于袋子的定义。 *)

(** **** 练习：1 星, standard (count_member_nonzero)  *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 下面这条关于 [leb] 的引理可助你完成下一个证明。 *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(** Before doing the next exercise, make sure you've filled in the
   definition of [remove_one] above. *)
(** **** 练习：3 星, advanced (remove_does_not_increase_count)  *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (bag_count_sum)  

    写下一个用到函数 [count] 和 [sum] 的，关于袋子的有趣定理 [bag_count_sum]，
    然后证明它。（你可能会发现该证明的难度取决于你如何定义 [count]！） *)
(* 请在此处解答 

    [] *)

(** **** 练习：4 星, advanced (rev_injective)  

    求证 [rev] 是单射函数，即：

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

    （这个问题既可以用简单的方式解决也可以用繁琐的方式来解决。） *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_rev_injective : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Options 可选类型 *)

(** 假设我们想要写一个返回某个列表中第 [n] 个元素的函数。如果我们为它赋予类型
    [nat -> natlist -> nat]，那么当列表太短时我们仍须返回某个数... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* 任意值！ *)
  | a :: l' => match n =? O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** 这种方案并不好：如果 [nth_bad] 返回了 [42]，那么不经过进一步处理的话，
    我们无法得知该值是否真的出现在了输入中。（译注：我们无法判断是什么因素让它返回了
    [42]，因为它可能是列表过短时的返回值，同时也可能是（此时列表足够长）在列表中找到的值）
    一种更好的方式是改变 [nth_bad] 的返回类型，使其包含一个错误值作为可能的结果。
    我们将此类型命名为 [natoption]。 *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

(** 然后我们可以修改前面 [nth_bad] 的定义，使其在列表太短时返回 [None]，
    在列表足够长且 [a] 在 [n] 处时返回 [Some a]。我们将这个新函数称为
    [nth_error] 来表明它可以产生带错误的结果。 *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** （在 HTML 版本中隐藏了这些老套的证明。若你想看它请点击小方格。）

    本例也是个介绍 Coq 编程语言更多细微特性的机会，比如条件表达式... *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.

 (** Coq 的条件语句和其它语言中的一样，不过加上了一点更为一般化的特性。
    由于布尔类型不是内建的，因此 Coq 实际上支持在_'任何'_带有两个构造子的，
    归纳定义的类型上使用条件表达式。当断言（guard）求值为 [Inductive]
    定义中的第一个构造子时，它被认为是真的；当它被求值到第二个构造子时，
    则被认为是假的。 *)

(** 以下函数从 [natoption] 中取出一个 [nat]，在遇到 [None] 时它将返回提供的默认值。 *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** 练习：2 星, standard (hd_error)  *)
 (** 用同样的思路修正之前的 [hd] 函数，使我们无需为 [nil] 的情况提供默认元素。  *)

Definition hd_error (l : natlist) : natoption
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* 请在此处解答 *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* 请在此处解答 *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (option_elim_hd)  *)
 (** 此练习能帮助你在新的 [hd_error] 和旧的 [hd] 之间建立联系。 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

End NatList.

(* ################################################################# *)
(** * 偏映射（Partial Maps） *)

(** 最后演示一下如何在 Coq 中定义基础的数据结构。这是一个简单的
    _'偏映射'_ 数据类型，它类似于大多数编程语言中的映射或字典数据结构。 *)

(** 首先，我们定义一个新的归纳数据类型 [id] 来用作偏映射的“键”。 *)

Inductive id : Type :=
  | Id (n : nat).

(** 本质上来说，[id] 只是一个数。但通过 [Id] 标签封装自然数来引入新的类型，
    能让定义变得更加可读，同时我们也可以灵活地按需修改它的定义。 *)

(** 我们还需要一个 [id] 的相等关系测试： *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(** **** 练习：1 星, standard (eqb_id_refl)  *)
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 现在我们定义偏映射的类型： *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(** 此声明可以读作：“有两种方式可以构造一个 [partial_map]：用构造子 [empty]
    表示一个空的偏映射，或通过将构造子 [record] 应用到一个键、一个值和一个既有的
    [partial_map] 来构造一个带“键-值”映射 的 [partial_map]。”*)

(** [update] 函数在部分映射中覆盖给定的键以取缔原值（如该键尚不存在，
    则新建其记录）。 *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** 最后，[find] 函数按照给定的键搜索一个 [partial_map]。若该键无法找到，
    它就返回 [None]；若该键与 [val] 相关联，则返回 [Some val]。
    若同一个键被映到多个值，[find] 就会返回它遇到的第一个值。 *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(** **** 练习：1 星, standard (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* 请在此处解答 *) Admitted.
(** [] *)
End PartialMap.

(** **** 练习：2 星, standard (baz_num_elts)  

    考虑以下归纳定义： *)

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(** 有_'多少'_个表达式具备类型 [baz]？（以注释说明。） *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_baz_num_elts : option (nat*string) := None.
(** [] *)

(* Fri Jul 19 00:32:19 UTC 2019 *)
