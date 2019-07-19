(** * Records: 为 STLC 添加记录体 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

(* ################################################################# *)
(** * 添加记录体 *)

(** 在 [MoreStlc] 一章中，我们了解到记录体（Record）
    可被视作嵌套使用的积类型的语法糖。对于简单的例子来说这样还行，
    然而其编码是非形式化的（实际上，如果我们真的以这种方式来对待记录体，
    那么它应该在解析器中处理，我们这里暂不考虑），总之它不太高效。
    因此了解如何将记录体作为语言中的一等公民仍然十分有趣。本章中展示了这种方法。

    请回忆我们之前给出的非形式化定义： *)

(**
    语法：

       t ::=                          项：
           | {i1=t1, ..., in=tn}         记录
           | t.i                         投影
           | ...

       v ::=                          值：
           | {i1=v1, ..., in=vn}         记录值
           | ...

       T ::=                          类型：
           | {i1:T1, ..., in:Tn}         记录类型
           | ...

   归约：

                               ti ==> ti'
  -------------------------------------------------------------------- (ST_Rcd)
  {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                                 t1 ==> t1'
                               --------------                        (ST_Proj1)
                               t1.i ==> t1'.i

                          -------------------------                (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi

   定型：

               Gamma |- t1 : T1     ...     Gamma |- tn : Tn
             --------------------------------------------------         (T_Rcd)
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                       Gamma |- t : {..., i:Ti, ...}
                       -----------------------------                   (T_Proj)
                             Gamma |- t.i : Ti
*)

(* ################################################################# *)
(** * 形式化记录体 *)

Module STLCExtendedRecords.

(* ----------------------------------------------------------------- *)
(** *** 语法和操作语义 *)

(** 要将记录体的语法形式化，最显然的方式是这样的： *)

Module FirstTry.

Definition alist (X : Type) := list (string * X).

Inductive ty : Type :=
  | Base     : string -> ty
  | Arrow    : ty -> ty -> ty
  | TRcd      : (alist ty) -> ty.

(** 然而，我们在这里遇到了 Coq 的限制：该类型无法自动给出我们期望的归纳法则，
    也就是说，[TRcd] 的情况中的归纳假设并未给出关于列表中的 [ty] 元素的任何信息，
    因此它对我们想要做的证明毫无用处。 *)

(* Check ty_ind.
   ====>
    ty_ind :
      forall P : ty -> Prop,
        (forall i : id, P (Base i)) ->
        (forall t : ty, P t -> forall t0 : ty, P t0
                            -> P (Arrow t t0)) ->
        (forall a : alist ty, P (TRcd a)) ->    (* ??? *)
        forall t : ty, P t
*)

End FirstTry.

(** 让 Coq 为我们生成更好的归纳法则是可能的，但是实现它的具体细节并不是很漂亮，
    我们得到的法则也不如 Coq 为简单的 [Inductive] 定义生成的法则那么直观易用。

    幸好，我们还能用另一种方式来形式化记录体，某种意义上说，它甚至更加简单和自然：
    我们并不使用 Coq 的标准 [list] 类型，而是在类型的语法中直接包含它的构造子
    （“nil”和“cons”）。 *)

Inductive ty : Type :=
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | RNil : ty
  | RCons : string -> ty -> ty -> ty.

(** 与此类似，在“项”这一层上，我们有空记录体构造子 [trnil]，
    以及将单个字段添加到字段列表之首的构造子 [rcons]。 *)

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (* 记录体 *)
  | rproj : tm -> string -> tm
  | trnil :  tm
  | rcons : string -> tm -> tm -> tm.

(** 一些例子…… *)
Open Scope string_scope.

Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := (Base "A").
Notation B := (Base "B").
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

(** [{ i1:A }] *)

(* Check (RCons i1 A RNil). *)

(** [{ i1:A->B, i2:A }] *)

(* Check (RCons i1 (Arrow A B)
           (RCons i2 A RNil)). *)

(* ----------------------------------------------------------------- *)
(** *** 良构性 *)

(** 在将记录体的抽象语法从列表推广为用 nil/cons 表示时会引入一个问题：
    我们可能写出如下这种奇怪的类型…… *)

Definition weird_type := RCons X A B.

(** 该记录类型的「尾部（tail）」并不是一个真正的记录类型！ *)

(** 我们要重构我们的类型断言，让 [weird_type] 这种病态的（ill-formed）类型不能被赋项。
    为此，我们定义了断言 [record_ty] 和 [record_tm] 来刻画了记录体的类型和项，
    以及 [well_formed_ty] 用于排除劣构的类型。 *)

(** 首先，如果某个类型在最外层只用 [RNil] 和 [RCons] 构造，那么它是一个记录。 *)

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty RNil
  | RTcons : forall i T1 T2,
        record_ty (RCons i T1 T2).

(** 据此，我们可以定义良构的（well-formed）类型。 *)

Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall i,
        well_formed_ty (Base i)
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (Arrow T1 T2)
  | wfRNil :
        well_formed_ty RNil
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty (RCons i T1 T2).

Hint Constructors record_ty well_formed_ty.

(** 需注意 [record_ty] 不是递归的：它只检查最外层的构造子。另一方面，
    [well_formed_ty] 这一性质就其“每个记录体的尾部（即 [RCons] 的第二个参数）
    都是记录体”的意义而言，保证了整个类型是良构的。

    当然，除了类型以外，我们还要考虑劣构的项。不过类型检查无需一个额外的
    [well_formed_tm] 定义就能排除它们，因为项的结构是经过了检查的。
    我们需要的只是类似 [record_ty] 的定义，即如果某个项以 [trnil] 和 [rcons]
    构造，那么它就是记录项。 *)

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : forall i t1 t2,
        record_tm (rcons i t1 t2).

Hint Constructors record_tm.

(* ----------------------------------------------------------------- *)
(** *** 代换 *)

(** 代换很容易扩展。 *)

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y => if eqb_string x y then s else t
  | abs y T t1 => abs y T
                     (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | rproj t1 i => rproj (subst x s t1) i
  | trnil => trnil
  | rcons i t1 tr1 => rcons i (subst x s t1) (subst x s tr1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ----------------------------------------------------------------- *)
(** *** 归约 *)

(** 如果一个记录体的所有字段都是值，那么它本身也是值。 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (rcons i v1 vr).

Hint Constructors value.

(** 为了定义归约，我们需要一个辅助函数来提取记录项中的某个字段： *)

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | rcons i' t tr' => if eqb_string i i' then Some t else tlookup i tr'
  | _ => None
  end.

(** [step] 函数会在投影规则中使用该项一级的查找函数。 *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> ([x:=v2]t12)
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        (rproj t1 i) --> (rproj t1' i)
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        (rproj tr i) --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        (rcons i t1 tr2) --> (rcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        (rcons i v1 tr2) --> (rcons i v1 tr2')

where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

(* ----------------------------------------------------------------- *)
(** *** 定型 *)

(** 接着我们定义定型规则。这些规则基本上直接转写自前面的推理规则，
    唯一明显的区别是对 [well_formed_ty] 的使用。在非形式化的表述中，
    我们使用了只允许良构记录类型的语法，因此我们无需添加单独的检查。

    我们需要维持一个合理的条件，就是只要 [has_type Gamma t T] 成立，那么
    [well_formed_ty T] 也应当成立，这样 [has_type] 就不会将劣构的类型赋予项了。
    我们后面会证明此定理。然而，我们并不想将 [has_type] 的定义和不必要的
    [well_formed_ty] 混在一起，而是只在需要的地方使用 [well_formed_ty] 检查：
    即在归纳调用 [has_type] 时不会检查类型良构性的地方使用它。例如，我们会在
    [T_Var] 的情况下检查 [well_formed_ty T]，因为这里没有归纳的 [has_type]
    调用来执行此操作。同样，在 [T_Abs] 的情况下，我们需要一个 [well_formed_ty T11]
    的证明，因为对 [has_type] 的归纳调用只能保证 [T12] 是良构的。 *)

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | RCons i' T Tr' =>
      if eqb_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (var x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (app t1 t2) \in T2
  (* records: *)
  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (rproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in RNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (rcons i t tr) \in (RCons i T Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(** ** 示例 *)

(** **** 练习：2 星, standard (examples)  

    完成下面的证明。在此证明中可随意使用 Coq 的自动化特性。然而，
    如果你不熟悉类型系统是如何工作的，那么应该先用基本策略来完成证明
    （比如使用 [apply] 而非 [eapply]），再试着用自动化特性来简化它。
    在证明之前，请先确保你理解它的意思。 *)

Lemma typing_example_2 :
  empty |-
    (app (abs a (RCons i1 (Arrow A A)
                      (RCons i2 (Arrow B B)
                       RNil))
              (rproj (var a) i2))
            (rcons i1 (abs a A (var a))
            (rcons i2 (abs a B (var a))
             trnil))) \in
    (Arrow B B).
Proof.
  (* 请在此处解答 *) Admitted.

Example typing_nonexample :
  ~ exists T,
      (update empty a (RCons i2 (Arrow A A)
                                RNil)) |-
               (rcons i1 (abs a B (var a)) (var a)) \in
               T.
Proof.
  (* 请在此处解答 *) Admitted.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (update empty y A) |-
           (app (abs a (RCons i1 A RNil)
                     (rproj (var a) i1))
                   (rcons i1 (var y) (rcons i2 (var y) trnil))) \in
           T.
Proof.
  (* 请在此处解答 *) Admitted.

(* ================================================================= *)
(** ** 定型的性质 *)

(** 对该系统可进性和保型性的证明与对纯粹的简单类型 λ-演算的基本相同，
    不过我们需要引入一些涉及记录体的引理来作的技术上处理。 *)

(* ----------------------------------------------------------------- *)
(** *** 良构性 *)

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* RCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (eqb_string i s)...
    inversion H0. subst...  Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
Qed.

(** *** 依字段查表*)

(** 引理：若 [empty |- v : T] 和 [Tlookup i T] 返回 [Some Ti]，
      则对于 [empty |- ti \in Ti] 的项 [ti]，[tlookup i v] 会返回 [Some ti]。

    证明：对定型导出式 [Htyp] 来归纳。由于 [Tlookup i T = Some Ti]，因此
      [T] 必为记录类型，据此以及 [v] 为值的观察，可以消除了部分情况，
      剩下的只有 [T_RCons] 的情况。

      定型导出式的最后一步是根据 [T_RCons] 得来的，那么对于某些 [i0]、[t]、[tr]、[T]
      和 [Tr] 来说，[t = rcons i0 t tr] 且 [T = RCons i0 T Tr]。

      现在还剩下两种情况需要考虑，即 [i0 = i] 是否成立。

      - 若 [i = i0]，那么根据 [Tlookup i (RCons i0 T Tr) = Some Ti]，我们有
        [T = Ti]。它根据 [t] 本身满足此定理得出。

      - 另一方面，假设 [i <> i0]。那么

        Tlookup i T = Tlookup i Tr

        且

        tlookup i t = tlookup i tr,

        则结果由归纳假设得出。 []

    以下为形式化证明：
*)

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember (@empty ty) as Gamma.
  induction Htyp; subst; try solve_by_invert...
  - (* T_RCons *)
    simpl in Hget. simpl. destruct (eqb_string i i0).
    + (* i is first *)
      simpl. inversion Hget. subst.
      exists t...
    + (* get tail *)
      destruct IHHtyp2 as [vi [Hgeti Htypi]]...
      inversion Hval... Qed.

(* ----------------------------------------------------------------- *)
(** *** 可进性 *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  (* 定理：假设 empty |- t : T。那么以下二者之一成立：
       1. t 为值，或者
       2. 对某个 t'，有 t --> t'。
     证明：对给定的定型导出式作归纳。 *)
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* 一给定的定型导出式的最后一条规则不能为 [T_Var]，因为它不应是
       [empty |- x : T] 的情况（因为上下文为空）。 *)
    inversion H.
  - (* T_Abs *)
    (* 若最后应用的规则为 [T_Abs]，则有 [t = abs x T11 t12]，它是一个值。 *)
    left...
  - (* T_App *)
    (* 若最后应用的规则为 T_App，则有 [t = t1 t2]。这点可由以下规则的形式得到：
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       根据归纳假设，t1 和 t2 要么是值，要么可再推进一步。 *)
    right.
    destruct IHHt1; subst...
    + (* t1 为值 *)
      destruct IHHt2; subst...
      * (* t2 为值 *)
      (* 若 [t1] 和 [t2] 均为值，那么我们知道
         [t1 = abs x T11 t12]，因为“抽象”是唯一具有箭头类型的值。
         然而根据 [ST_AppAbs]，[(abs x T11 t12) t2 --> [x:=t2]t12]。 *)
        inversion H; subst; try solve_by_invert.
        exists ([x:=t2]t12)...
      * (* t2 推进一步 *)
        (* 若 [t1] 为值且 [t2 --> t2']，那么根据 [ST_App2]，
           [t1 t2 --> t1 t2']。 *)
        destruct H0 as [t2' Hstp]. exists (app t1 t2')...
    + (* t1 推进一步 *)
      (* 最后，若 [t1 --> t1']，那么根据 [ST_App1]，[t1 t2 --> t1' t2]。 *)
      destruct H as [t1' Hstp]. exists (app t1' t2)...
  - (* T_Proj *)
    (* 若给定导出式的最后一条规则为 [T_Proj]，那么
       [t = rproj t i] 且 [empty |- t : (TRcd Tr)]
       根据归纳假设，[t] 要么是值，要么可以推进一步。 *)
    right. destruct IHHt...
    + (* rcd 为值 *)
      (* 若 [t] 为值，那么我们可使用引理 [lookup_field_in_value]
         来证明对某个 [ti] 而言 [tlookup i t = Some ti]。根据
         [ST_ProjRcd] 可得 [rproj i t --> ti]。 *)
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H)
        as [ti [Hlkup _]].
      exists ti...
    + (* rcd 推进一步 *)
      (* 另一方面，若 [t --> t']，那么根据 [ST_Proj1] 可得
         [rproj t i --> rproj t' i]。 *)
      destruct H0 as [t' Hstp]. exists (rproj t' i)...
  - (* T_RNil *)
    (* 若给定导出式中的最后一条规则为 [T_RNil]，那么 [t = trnil]，为值。 *)
    left...
  - (* T_RCons *)
    (* 若最后一条规则为 [T_RCons]，那么 [t = rcons i t tr] 且
         [empty |- t : T]
         [empty |- tr : Tr]
       根据归纳法则，[t] 和 [tr] 要么是值，要么可再推进一步。 *)
    destruct IHHt1...
    + (* head 为值 *)
      destruct IHHt2; try reflexivity.
      * (* tail 为值 *)
      (* 若 [t] 和 [tr] 均为值，那么 [rcons i t tr] 也为值。 *)
        left...
      * (* tail 推进一步 *)
        (* 若 [t] 为值且 [tr --> tr']，那么根据 [ST_Rcd_Tail]，
           [rcons i t tr --> rcons i t tr']。 *)
        right. destruct H2 as [tr' Hstp].
        exists (rcons i t tr')...
    + (* head 推进一步 *)
      (* 若 [t --> t']，那么根据 [ST_Rcd_Head]，
         [rcons i t tr --> rcons i t' tr]。 *)
      right. destruct H1 as [t' Hstp].
      exists (rcons i t' tr)...  Qed.

(* ----------------------------------------------------------------- *)
(** *** 上下文不变性 *)

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
  | afi_proj : forall x t i,
     appears_free_in x t ->
     appears_free_in x (rproj t i)
  | afi_rhead : forall x i ti tr,
      appears_free_in x ti ->
      appears_free_in x (rcons i ti tr)
  | afi_rtail : forall x i ti tr,
      appears_free_in x tr ->
      appears_free_in x (rcons i ti tr).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold update, t_update. destruct (eqb_stringP x y)...
  - (* T_App *)
    apply T_App with T1...
  - (* T_RCons *)
    apply T_RCons...  Qed.

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
Qed.

(* ----------------------------------------------------------------- *)
(** *** 保型性 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (update Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  (* 定理：若 x|->U;Gamma |- t : S 且 empty |- v : U，则
     Gamma |- ([x:=v]t) S。 *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  (* 证明：通过对项 t 作归纳可得。大部分情况下，结论可以从归纳假设直接得到，
     只有 var、abs 和 rcons 的情况需要额外证明。无法自动得到前两者，
     是因为我们必须处理变量之间的相互作用。对于 rcons 的情况，
     我们必须额外证明在项中作代换不改变它是否为一个记录项。 *)
  induction t;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  - (* var *)
    simpl. rename s into y.
    (* 若 t = y，我们知道
         [empty |- v : U] 且
         [x|->U; Gamma |- y : S]
       经反演可得 [update Gamma x U y = Some S]。
       我们需要证明 [Gamma |- [x:=v]y : S]。

       有两种情况需要考虑：[x=y] 或 [x<>y]。 *)
    unfold update, t_update in H0.
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
    (* 若 [x = y]，那么我们知道 [U = S]，以及 [[x:=v]y = v]。
       因此我们必须证明若 [empty |- v : U] 则 [Gamma |- v : U]。
       我们已经证明了此定理更一般的版本，即上下文不变性！ *)
      subst.
      inversion H0; subst. clear H0.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
      inversion HT'.
    + (* x<>y *)
    (* 若 [x <> y]，则 [Gamma y = Some S] 且代换没有效果。我们可以根据
       [T_Var] 证明 [Gamma |- y : S]。 *)
      apply T_Var...
  - (* abs *)
    rename s into y. rename t into T11.
    (* 若 [t = abs y T11 t0]，那么我们知道
         [x|->U; Gamma |- abs y T11 t0 : T11->T12]
         [x|->U; y|->T11; Gamma |- t0 : T12]
         [empty |- v : U]
       根据归纳假设，我们知道对于所有的 S Gamma，
         [x|->U; Gamma |- t0 : S -> Gamma |- [x:=v]t0 S].

       我们可以计算出
       [ [x:=v]t = abs y T11 (if eqb_string x y then t0 else [x:=v]t0) ]，
       此时我们必须证明 [Gamma |- [x:=v]t : T11->T12]。我们知道可以用
       [T_Abs] 来证明它，因此接下来需要证明的就是：
         [y|->T11; Gamma |- if eqb_string x y then t0 else [x:=v]t0 : T12]
       我们考虑两种情况：[x = y] 和 [x <> y]。 *)
    apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      (* 若 [x = y]，则代换没有作用。上下文不变性保证了
         [y:U,y:T11] 和 [Gamma,y:T11] 等价。在前者的上下文中有 [t0 : T12] ，
         那么在后者中也是这样。 *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + (* x<>y *)
      (* 若 [x <> y]，那么归纳假设和上下文不变性能让我们证明
           [x|->U; y|->T11; Gamma |- t0 : T12]       =>
           [y|->T11; x|->U; Gamma |- t0 : T12]       =>
           [y|->T11; Gamma |- [x:=v]t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst. rewrite false_eqb_string...
  - (* rcons *)
    apply T_RCons... inversion H7; subst; simpl...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t --> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* 定理：若 [empty |- t : T] 且 [t --> t']，则
     [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* 证明：对给定的定型导出式来归纳。很多情况是矛盾的（[T_Var]、[T_Abs]）
     或可直接从归纳假设得出（[T_RCons]），我们只需证明那些“有趣”的情况。 *)
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    (* 若使用的最后一条规则为 [T_App]，那么 [t = t1 t2]。
       证明 [t --> t'] 可能用到的三条规则是 [ST_App1]、[ST_App2] 和 [ST_AppAbs]。
       在前两种情况下，结果可直接从归纳假设得出。 *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      (* 对于第三种情况，假设
           [t1 = abs x T11 t12]
         且
           [t2 = v2]。我们必须证明 [empty |- [x:=v2]t12 : T2]。
         根据假设我们知道
             [empty |- abs x T11 t12 : T1->T2]
         经反演可得
             [x:T1 |- t12 : T2]
         我们已经证明了 substitution_preserves_typing，又根据假设，有
             [empty |- v2 : T1]
         故此分支证明完毕。 *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  - (* T_Proj *)
    (* 若 [T_Proj]，则 [t = rproj t1 i]。
       证明 [t --> t'] 需要两条规则：[T_Proj1] 和 [T_ProjRcd]。
       [t'] 的定型可从前面情况中的归纳假设得出，因此我们只需考虑
       [T_ProjRcd]  即可。

       这里我们知道 [t] 为记录体值。由于使用了规则 [T_Proj]，
       我们知道对于某些 [i] 和 [Tr] 有 [empty |- t \in Tr] 且
       [Tlookup i Tr = Some Ti]。接着可以应用引理 [lookup_field_in_value]
       来查找该投影步骤所得的记录元素。 *)
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp]].
    rewrite H4 in Hget. inversion Hget. subst...
  - (* T_RCons *)
    (* 若最后一条规则为 [T_RCons]，那么对于某些 [i]、[t] 和满足
       [record_tm tr] 的 [tr]，有 [t = rcons i t tr]。若该步骤为
       [ST_Rcd_Head]，则结果可由归纳假设直接得出。若该步骤为
       [ST_Rcd_Tail]，那么对于某些 [tr2'] 有 [tr --> tr2']，
       我们还需要使用引理 [step_preserves_record_tm] 来证明 [record_tm tr2']。 *)
    apply T_RCons... eapply step_preserves_record_tm...
Qed.
(** [] *)

End STLCExtendedRecords.

(* Fri Jul 19 00:33:16 UTC 2019 *)
