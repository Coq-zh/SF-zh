(** * ImpCEvalFun: Imp 的求值函数 *)

(** 在[Imp]一章中我们已经见到了直接为 [Imp] 定义求值函数时会遇到的困难。
    当时为了规避这些困难，我们选择了定义求值关系而不是函数。
    而在这一可选的章节中，我们会再次讨论能够实现 [Imp] 求值函数的方法。 *)

(* ################################################################# *)
(** * 一个无法完成的求值器 *)

From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
From LF Require Import Imp Maps.

(** 在初次为指令编写求值函数时，我们写出了如下忽略了 [WHILE] 的代码： *)

Open Scope imp_scope.
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        (l !-> aeval st a1 ; st)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st  (* bogus *)
  end.
Close Scope imp_scope.

(** 如[Imp]一章中所言，在 ML 或 Haskell 这类传统的函数式语言中，
  我们可以这样处理 [WHILE] 指令：

    | WHILE b1 DO c1 END =>
        if (beval st b1) then
          ceval_step1 st (c1;; WHILE b1 DO c1 END)
        else st

    Coq 不会接受此定义（它会提示出现错误 [Error: Cannot guess
    decreasing argument of fix]），因为我们想要定义的函数无需保证一定停机。
    确实，修改后的 [ceval_step1] 应用到 [Imp.v] 中的 [loop] 程序时永远不会停机。
    因为 Coq 不仅是一个函数式编程语言，还拥有逻辑一致性，
    因此任何有可能不会停机的函数都会被拒绝。下面是一段无效的(!) Coq
    程序，它展示了假如 Coq 允许不停机的递归函数时会产生什么错误：

     Fixpoint loop_false (n : nat) : False := loop_false n.

    也就是说，像 [False] 这样的命题会变成可证的（例如 [loop_false 0]
    就是个对 [False] 的证明），这对 Coq 的逻辑一致性来说是一场灾难。

    由于它不会对所有的输入停机，因此至少在不借助附加技巧的情况下，
    [ceval_step1] 的完整版本无法用 Coq 写出... *)

(* ################################################################# *)
(** * 一个计步的求值器 *)

(** 我们需要的技巧是将一个_'附加'_的参数传入求值函数中来告诉它需要运行多久。
    非正式地说，我们会在求值器的“油箱”中加一定数量的“汽油”，
    然后允许它运行到按一般的方式终止_'或者'_耗尽汽油，
    此时我们会停止求值并说最终结果为空内存（empty memory）。
    （我们也可以说当前的状态为求值器耗尽了汽油 -- 这无关紧要，
    因为无论在哪种情况下结果都是错误的！） *)

Open Scope imp_scope.
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.
Close Scope imp_scope.

(** _'注意'_：很容易想到这里的索引 [i] 是用来计算“求值的步数”的。
    然而我们仔细研究就会发现实际并非如此。例如，在串连的规则中，同一个
    [i] 被传入了两个递归调用中。正确地理解 [i] 对于 [ceval__ceval_step]
    的正式名分重要，它会在下面的练习中给出。

    此求值器不太好的一点就是我们无法根据其结果说它是否停止，
    因为程序可能是正常停机，也可能是耗尽了汽油。我们的下下一个版本会返回一个
    [option state] 而非只是一个 [state]，这样我们就能区分正常和异常的停机了。 *)

Open Scope imp_scope.
Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.
Close Scope imp_scope.

(** 我们可以引入一些辅助记法来隐藏对可选状态进行重复匹配的复杂工作，
    从而提高此版本的可读性。 *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

(* Compute
     (test_ceval empty_st
         (X ::= 2;;
          TEST (X <= 1)
            THEN Y ::= 3
            ELSE Z ::= 4
          FI)).
   ====>
      Some (2, 0, 4)   *)

(** **** 练习：2 星, standard, recommended (pup_to_n)  

    编写一个 Imp 程序对 [1] 到 [X] 求和（即 [1 + 2 + ... + X]）并赋值给 [Y]。
    确保你的解答能满足之后的测试。 *)

Definition pup_to_n : com
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(* 

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

    [] *)

(** **** 练习：2 星, standard, optional (peven)  

    编写一个 [Imp] 程序：该程序在 [X] 为偶数时将 [Z] 置为 [0]，
    否则将 [Z] 置为 [1]。使用 [test_ceval] 测试你的程序。 *)

(* 请在此处解答 

    [] *)

(* ################################################################# *)
(** * 关系求值 vs. 计步求值 *)

(** 对于算术表达式和布尔表达式，我们希望两种求值的定义最终都能产生同样的结果。
    本节将对此说明。 *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.

      + (* ;; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.

      + (* TEST *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1. intros H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.

(** **** 练习：4 星, standard (ceval_step__ceval_inf)  

    按照通常的模版写出 [ceval_step__ceval] 的非形式化证明，
    （对归纳定义的值进行分类讨论的模版，除了没有归纳假设外，
    应当看起来与归纳证明相同。）不要简单地翻译形式化证明的步骤，
    请让你的证明能够将主要想法传达给读者。 *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_ceval_step__ceval_inf : option (nat*string) := None.
(** [] *)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.

    + (* TEST *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval.  Qed.

(** **** 练习：3 星, standard, recommended (ceval__ceval_step)  

    请完成以下证明。你会在某些地方用到 [ceval_step_more] 以及一些关于
    [<=] 和 [plus] 的基本事实。 *)

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  (* 请在此处解答 *) Admitted.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ################################################################# *)
(** * 再论求值的确定性 *)

(** 根据关系求值和计步求值的定义等价这一事实，
    我们可以给出一种取巧的方式来证明求值_'关系'_是确定性的。 *)

Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.  Qed.

(* Fri Jul 19 00:32:21 UTC 2019 *)
