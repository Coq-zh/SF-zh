(** * Maps: 全映射与偏映射 *)

(** _'映射（Map）'_（或_'字典（Dictionary）'_）是一种非常普遍的数据结构，
    在编程语言理论中尤甚，而之后的章节中我们会多次用到它。
    映射也适合运用之前学过的概念进行研究，包括如何在高阶函数之外构建数据结构
    （见 [Basics] 和 [Poly]）以及通过互映来精简证明（见 [IndProp]）。

    我们会定义两种映射：在查找的键不存在时，_'全映射'_会返回“默认”元素，
    而_'偏映射'_则会返回一个 [option] 来指示成功还是失败。后者根据前者来定义，
    它使用 [None] 默认元素。 *)

(* ################################################################# *)
(** * Coq 标准库 *)

(** 开始前的小插话...

    和我们目前学过的章节不同，本章无需通过 [Require Import] 导入之前的章节
    （自然也就不会间接导入更早的章节）。从本章开始，我们我们将直接从
    Coq 标准库中导入需要的定义和定理。然而应该不会注意到多大差别，
    因为我们一直小心地将自己的定义和定理的命名与标准库中的部分保持一致，
    无论它们在哪里重复。 *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(** 标准库的文档见
    https://coq.inria.fr/library/。

    [Search] 指令可用于查找涉及具体类型对象的定理。我们花点时间来熟悉一下它。 *)

(* ################################################################# *)
(** * 标识符 *)

(** 首先我们需要键的类型来对映射进行索引。在 [Lists.v] 中，
    我们为类似的目的引入了 [id] 类型。而在_'《软件基础》'_后面的部分，
    我们会使用 Coq 标准库中的 [string] 类型。 *)

(** 为了比较字符串，我们定义了 [eqb_string] 函数，它在内部使用 Coq
    字符串库中的 [string_dec] 函数。 *)


Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(** （函数 [string_dec] 来自于 Coq 的字符串标准库。如果你查看
    [string_dec] 的结果类型，就会发现其返回值的类型并不是 [bool]，
    而是一个形如 [{x = y} + {x <> y}] 的类型，叫做 [sumbool] 类型，
    它可以看做“带有证据的布尔类型”。形式上来说，一个 [sumbool]
    类型的元素要么是两个东西相等的证明，要么就是它们不相等的证明，
    与一个标签一起来指出具体是哪一个。不过就目前来说，你可以把它当做一个
    花哨的 [bool]。） *)

(** 现在我们需要一些关于字符串相等性的基本性质... *)
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

(** 以下有用的性质可由类似的字符串引理推出： *)

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

(** 类似地： *)

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** 以下方便使用的变体只需通过改写就能得出： *)

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * 全映射 *)

(** 在本章中，我们的主要任务就是构建一个偏映射的定义，其行为类似于我们之前在
    [Lists]一章中看到的那个，再加上伴随其行为的引理。

    不过这一次，我们将使用_'函数'_而非“键-值”对的列表来构建映射。
    这种表示方法的优点在于它提供了映射更具_'外延性'_的视角，
    即以相同方式回应查询的两个映射将被表示为完全相同的东西（即一摸一样的函数），
    而非只是“等价”的数据结构。这反过来简化了使用映射的证明。 *)

(** 我们会分两步构建偏映射。首先，我们定义一个_'全映射'_类型，
    它在某个映射中查找不存在的键时会返回默认值。 *)

Definition total_map (A : Type) := string -> A.

(** 直观上来说，一个元素类型为 [A] 的全映射不过就是个根据 [string]
    来查找 [A] 的函数。 *)

(** 给定函数 [t_empty] 一个默认元素，它会产生一个空的全映射。
    此映射在应用到任何字符串时都会返回默认元素。 *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** 更有趣的是 [update] 函数，它和之前一样，接受一个映射 [m]、一个键 [x]
    以及一个值 [v]，并返回一个将 [x] 映射到 [v] 的新映射；其它键则与
    [m] 中原来的保持一致。 *)

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

(** 此定义是个高阶编程的好例子：[t_update] 接受一个_'函数'_ [m]
    并产生一个新的函数 [fun x' => ...]，它的表现与所需的映射一致。 *)

(** 例如，我们可以构建一个从 [string] 到 [bool] 的映射，其中 ["foo"]
    和 ["bar"] 映射到 [true]，其它键则映射到 [false]，就像这样： *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** 接下来，我们引入一些新的记法来方便映射的使用。 *)

(** 首先，我们会使用以下记法，根据一个默认值来创建空的全映射。 *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** 然后，我们引入一种方便的记法，通过一些绑定来扩展现有的映射。 *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** 前面的 [examplemap] 现在可以定义如下： *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(** 到这里就完成了全映射的定义。注意我们无需定义 [find] 操作，
    因为它不过就是个函数应用！ *)

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** 为了在后面的章节中使用映射，我们需要一些关于其表现的基本事实。 *)

(** 即便你没有进行下面的练习，也要确保透彻地理解以下引理的陈述！ *)

(** （其中有些证明需要函数的外延性公理，我们在[Logic]一节中讨论过它）。 *)

(** **** 练习：1 星, standard, optional (t_apply_empty)  

    首先，空映射对于所有的键都会返回默认元素（即，空映射总是返回默认元素）： *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (t_update_eq)  

    接着，如果将映射 [m] 的键 [x] 关联的值更新为 [v]，然后在 [update]
    产生的新映射中查找 [x]，就会得到 [v]（即，更新某个键的映射，
    查找它就会得到更新后的值）： *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (t_update_neq)  

    此外，如果将映射 [m] 的键 [x1] 更新后在返回的结果中查找_'另一个'_键
    [x2]，那么得到的结果与在 [m] 中查找它的结果相同
    （即，更新某个键的映射，不影响其它键的映射）： *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (t_update_shadow)  

    如果将映射 [m] 的键 [x] 关联的值更新为 [v1] 后，又将同一个键 [x]
    更新为另一个值 [v2]，那么产生的映射与仅将第二次 [update] 应用于 [m]
    所得到的映射表现一致（即二者应用到同一键时产生的结果相同）： *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 对于最后两个全映射的引理而言，用[IndProp]一章中引入的互映法
    （Reflection idioms）来证明会十分方便。我们首先通过证明基本的_'互映引理'_，
    将 [id] 上的相等关系命题与布尔函数 [eqb_id] 关联起来。*)

(** **** 练习：2 星, standard, optional (eqb_stringP)  

    请仿照[IndProp]一章中对 [eqb_natP] 的证明来证明以下引理： *)

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** 现在，给定 [string] 类型的字符串 [x1] 和 [x2]，我们可以在使用策略
    [destruct (eqb_stringP x1 x2)] 对 [eqb_string x1 x2]
    的结果进行分类讨论的同时，生成关于 [x1] 和 [x2] （在 [=] 的意义上）
    的相等关系前提。 *)

(** **** 练习：2 星, standard (t_update_same)  

    请仿照[IndProp]一章中的示例，用 [eqb_stringP] 来证明以下定理，
    它陈述了：如果我们用映射 [m] 中已经与键 [x] 相关联的值更新了 [x]，
    那么其结果与 [m] 相等： *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, recommended (t_update_permute)  

    使用 [eqb_stringP] 来证明最后一个 [update] 函数的性质：
    如果我们更新了映射 [m] 中两个不同的键，那么更新的顺序无关紧要。 *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 偏映射 *)

(** 最后，我们在全映射之上定义_'偏映射'_。元素类型为 [A] 的偏映射不过就是个
    元素类型为 [option A]，默认元素为 [None] 的全映射。 *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** 我们为偏映射引入类似的记法。 **)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** 当最后一种情况为空时，我们也可以隐藏它。 *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(** 现在我们将所有关于全映射的基本引理直接转换成对应的偏映射引理。 *)

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

(* Fri Jul 19 00:33:13 UTC 2019 *)
