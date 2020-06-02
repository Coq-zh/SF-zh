(** * Multiset:  Insertion Sort With Multisets *)

(** We have seen how to specify algorithms on "collections", such as
    sorting algorithms, using permutations.  Instead of using
    permutations, another way to specify these algorithms is to use
    multisets.  A _set_ of values is like a list with no repeats where
    the order does not matter.  A _multiset_ is like a list, possibly
    with repeats, where the order does not matter.  One simple
    representation of a multiset is a function from values to [nat]. *)

From Coq Require Import Strings.String.
From VFA Require Import Perm.
From VFA Require Import Sort.
Require Export FunctionalExtensionality.

(** In this chapter we will be using natural numbers for two different
    purposes: the values in the lists that we sort, and the
    multiplicity (number of times occurring) of those values.  To keep
    things straight, we'll use the [value] type for values, and [nat]
    for multiplicities. *)

Definition value := nat.

Definition multiset := value -> nat.

(** Just like sets, multisets have operators for [union], for the
    [empty] multiset, and the multiset with just a single element. *)

Definition empty : multiset :=
   fun x => 0.

Definition union (a b : multiset) : multiset :=
   fun x => a x + b x.

Definition singleton (v: value) : multiset :=
   fun x => if x =? v then 1 else 0.

(** **** 练习：1 星, standard (union_assoc) 

    Since multisets are represented as functions, to prove that one
    multiset equals another we must use the axiom of functional
    extensionality. *)

Lemma union_assoc: forall a b c : multiset, (* assoc stands for "associative" *)
   union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard (union_comm)  *)
Lemma union_comm: forall a b : multiset,  (* comm stands for "commutative" *)
   union a b = union b a.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** Remark on efficiency:  These multisets aren't very efficient.  If
  you wrote programs with them, the programs would run slowly. However,
  we're using them for _specifications_, not for _programs_.  Our
  multisets built with [union] and [singleton] will never really
  _execute_ on any large-scale inputs; they're only used in the proof
  of correctness of algorithms such as [sort].  Therefore, their
  inefficiency is not a problem. *)

(** Contents of a list, as a multiset: *)

Fixpoint contents (al: list value) : multiset :=
  match al with
  | a :: bl => union (singleton a) (contents bl)
  | nil => empty
  end.

(** Recall the insertion-sort program from [Sort.v].  Note that it
    handles lists with repeated elements just fine. *)

Example sort_pi: sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.

Example sort_pi_same_contents:
    contents (sort [3;1;4;1;5;9;2;6;5;3;5]) = contents [3;1;4;1;5;9;2;6;5;3;5].
Proof.
extensionality x.
do 10 (destruct x; try reflexivity).
  (* Why does this work? Try it step by step, without [do 10] *)
Qed.

(* ################################################################# *)
(** * Correctness *)

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.  But let's say that a different way: the
    algorithm must produce a list _with the same multiset of values_,
    and this list must be totally ordered. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, contents al = contents (f al) /\ sorted (f al).

(** **** 练习：3 星, standard (insert_contents) 

    First, prove the auxiliary lemma [insert_contents], which will be
    useful for proving [sort_contents] below.  Your proof will be by
    induction.  You do not need to use [extensionality]. *)

Lemma insert_contents: forall x l, contents (x::l) = contents (insert x l).
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (sort_contents) 

    Now prove that sort preserves contents. *)

Theorem sort_contents: forall l, contents l = contents (sort l).
(* 请在此处解答 *) Admitted.
(** [] *)

(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
split. apply sort_contents. apply sort_sorted.
Qed.

(** **** 练习：1 星, standard (permutations_vs_multiset) 

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_contents, sort_contents].  Which proofs are simpler?

      - [ ] easier with permutations,
      - [ ] easier with multisets
      - [ ] about the same.

   Regardless of "difficulty", which do you prefer / find easier to
   think about?
      - [ ] permutations or
      - [ ] multisets

   Put an X in one box in each list. *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Permutations and Multisets *)

(** The two specifications of insertion sort are equivalent.  One
    reason is that permutations and multisets are closely related.
    We're going to prove:

       [Permutation al bl <-> contents al = contents bl.] *)

(** **** 练习：3 星, standard (perm_contents) 

    The forward direction is easy, by induction on the evidence for
    [Permutation]: *)

Lemma perm_contents:
  forall al bl : list nat,
   Permutation al bl -> contents al = contents bl.
(* 请在此处解答 *) Admitted.
(** [] *)

(** The other direction,
    [contents al = contents bl -> Permutation al bl],
    is surprisingly difficult.  (Or maybe there's an easy way
    that I didn't find.) *)

Fixpoint list_delete (al: list value) (v: value) :=
  match al with
  | x::bl => if x =? v then bl else x :: list_delete bl v
  | nil => nil
  end.

Definition multiset_delete (m: multiset) (v: value) :=
   fun x => if x =? v then pred(m x) else m x.

(** **** 练习：3 星, standard (delete_contents)  *)
Lemma delete_contents:
  forall v al,
   contents (list_delete al v) = multiset_delete (contents al) v.
Proof.
  intros.
  extensionality x.
  induction al.
  simpl. unfold empty, multiset_delete.
  bdestruct (x =? v); auto.
  simpl.
  bdestruct (a =? v).
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (contents_perm_aux)  *)
Lemma contents_perm_aux:
 forall v b, empty = union (singleton v) b -> False.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (contents_in)  *)
Lemma contents_in:
  forall (a: value) (bl: list value) , contents bl a > 0 -> In a bl.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (in_perm_delete)  *)
Lemma in_perm_delete:
  forall a bl,
  In a bl -> Permutation (a :: list_delete bl a) bl.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard (contents_perm)  *)
Lemma contents_perm:
 forall al bl, contents al = contents bl -> Permutation al bl.
Proof.
  induction al; destruct bl; intro.
  auto.
  simpl in H.
  contradiction (contents_perm_aux _ _ H).
  simpl in H. symmetry in H.
  contradiction (contents_perm_aux _ _ H).
  specialize (IHal (list_delete (v :: bl) a)).
  remember (v::bl) as cl.
  clear v bl Heqcl.

  (** From this point on, you don't need induction.
    Use the lemmas [perm_trans], [delete_contents],
     [in_perm_delete], [contents_in].   At _certain points_
     you'll need to unfold the definitions of
     [multiset_delete], [union], [singleton]. *)

  (* 请在此处解答 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * The Main Theorem: Equivalence of Multisets and Permutations *)
Theorem same_contents_iff_perm:
  forall al bl, contents al = contents bl <-> Permutation al bl.
Proof.
  intros. split. apply contents_perm. apply perm_contents.
Qed.

(** Therefore, it doesn't matter whether you prove your sorting
    algorithm using the Permutations method or the multiset method. *)

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply same_contents_iff_perm; auto.
Qed.

(* 2020-06-02 03:42:00 (UTC+00) *)
