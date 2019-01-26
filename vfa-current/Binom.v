(** * Binom: Binomial Queues *)

(** Implementation and correctness proof of fast mergeable priority queues
   using binomial queues.

  Operation [empty] is constant time,  [insert], [delete_max], and [merge]
  are logN time.  (Well, except that comparisons on [nat] take linear time.
  Read the [Extract] chapter to see what can be done about that.) *)

(* ################################################################# *)
(** * Required Reading 
  Binomial Queues http://www.cs.princeton.edu/~appel/Binom.pdf
  by Andrew W. Appel, 2016.

  Binomial Queues http://www.cs.princeton.edu/~appel/BQ.pdf
  Section 9.7 of _Algorithms 3rd Edition in Java, Parts 1-4:
    Fundamentals, Data Structures, Sorting, and Searching_,
  by Robert Sedgewick.  Addison-Wesley, 2002.
*)

(* ################################################################# *)
(** * The Program *)

From Coq Require Import Strings.String.
From VFA Require Import Perm.
From VFA Require Import Priqueue.

Module BinomQueue <: PRIQUEUE.

Definition key := nat.

Inductive tree : Type :=
|  Node: key -> tree -> tree -> tree
|  Leaf : tree.

(** A priority queue (using the binomial queues data structure) is a
   list of trees.  The [i]'th element of the list is either [Leaf] or
   it is a power-of-2-heap with exactly [2^i] nodes.

  This program will make sense to you if you've read the Sedgewick
  reading; otherwise it is rather mysterious.
*)

Definition priqueue := list tree.

Definition empty : priqueue := nil.

Definition smash (t u:  tree) : tree :=
  match t , u with
  |  Node x t1 Leaf, Node y u1 Leaf =>
                   if  x >? y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf  (* arbitrary bogus tree *)
  end.

Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf        => nil
  | nil, _            => t :: nil
  | Leaf :: q', _  => t :: q'
  | u :: q', Leaf  => u :: q'
  | u :: q', _       => Leaf :: carry q' (smash t u)
 end.

Definition insert (x: key) (q: priqueue) : priqueue :=
     carry q (Node x Leaf Leaf).

Eval compute in fold_left (fun x q =>insert q x) [3;1;4;1;5;9;2;3;5] empty.
(** 
    = [Node 5 Leaf Leaf;
       Leaf;
       Leaf;
       Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf)))
          Leaf]
     : priqueue
>> *)

Fixpoint join (p q: priqueue) (c: tree) : priqueue :=
  match p, q, c with
    [], _ , _            => carry q c
  | _, [], _             => carry p c
  | Leaf::p', Leaf::q', _              => c :: join p' q' Leaf
  | Leaf::p', q1::q', Leaf            => q1 :: join p' q' Leaf
  | Leaf::p', q1::q', Node _ _ _  => Leaf :: join p' q' (smash c q1)
  | p1::p', Leaf::q', Leaf            => p1 :: join p' q' Leaf
  | p1::p', Leaf::q',Node _ _ _   => Leaf :: join p' q' (smash c p1)
  | p1::p', q1::q', _                   => c :: join p' q' (smash p1 q1)
 end.

Fixpoint unzip (t: tree) (cont: priqueue -> priqueue) : priqueue :=
  match t with
  |  Node x t1 t2   => unzip t2 (fun q => Node x t1 Leaf  :: cont q)
  | Leaf => cont nil
  end.

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
    Node x t1 Leaf  => unzip t1 (fun u => u)
  | _ => nil   (* bogus value for ill-formed or empty trees *)
  end.

Fixpoint find_max' (current: key) (q: priqueue) : key :=
  match q with
  |  []         => current
  | Leaf::q' => find_max' current q'
  | Node x _ _ :: q' => find_max' (if x >? current then x else current) q'
  end.

Fixpoint find_max (q: priqueue) : option key :=
  match q with
  | [] => None
  | Leaf::q' => find_max q'
  | Node x _ _ :: q' => Some (find_max' x q')
 end.

Fixpoint delete_max_aux (m: key) (p: priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p'   => let (j,k) := delete_max_aux m p'  in (Leaf::j, k)
  | Node x t1 Leaf :: p' =>
       if m >? x
       then (let (j,k) := delete_max_aux m p'
             in (Node x t1 Leaf::j,k))
       else (Leaf::p', heap_delete_max (Node x t1 Leaf))
  | _ => (nil, nil) (* Bogus value *)
  end.

Definition delete_max (q: priqueue) : option (key * priqueue) :=
  match find_max q with
  | None => None
  | Some  m => let (p',q') := delete_max_aux m q
                            in Some (m, join p' q' Leaf)
  end.

Definition merge (p q: priqueue) := join p q Leaf.

(* ################################################################# *)
(** * Characterization Predicates *)

(** [t] is a complete binary tree of depth [n], with every key <= [m] *)

Fixpoint pow2heap' (n: nat) (m: key) (t: tree) :=
 match n, m, t with
    0, m, Leaf       => True
  | 0, m, Node _ _ _  => False
  | S _, m,Leaf    => False
  | S n', m, Node k l r  =>
       m >= k /\ pow2heap' n' k l /\ pow2heap' n' m r
 end.

(** [t] is a power-of-2 heap of depth [n] *)

Definition pow2heap (n: nat) (t: tree) :=
  match t with
    Node m t1 Leaf => pow2heap' n m t1
  | _ => False
  end.

(** [l] is the [i]th tail of a binomial heap *)

Fixpoint priq'  (i: nat) (l: list tree) : Prop :=
   match l with
  | t :: l' => (t=Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
 end.

(** [q] is a binomial heap *)

Definition priq (q: priqueue) : Prop := priq' 0 q.

(* ################################################################# *)
(** * Proof of Algorithm Correctness *)

(* ================================================================= *)
(** ** Various Functions Preserve the Representation Invariant *)

(** ...that is, the [priq] property, or the closely related property [pow2heap].
*)

(** **** 练习：1 星, standard (empty_priq)   *)
Theorem empty_priq: priq empty.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (smash_valid)  *)
Theorem smash_valid:
       forall n t u, pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (carry_valid)  *)
Theorem carry_valid:
           forall n q,  priq' n q ->
           forall t, (t=Leaf \/ pow2heap n t) -> priq' n (carry q t).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (insert_valid)  *)
Theorem insert_priq: forall x q, priq q -> priq (insert x q).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard, optional (join_valid)  *)
(* This proof is rather long, but each step is reasonably straightforward.
    There's just one [induction] to do, right at the beginning. *)
Theorem join_valid: forall p q c n, priq' n p -> priq' n q -> (c=Leaf \/ pow2heap n c) -> priq' n (join p q c).
(* 请在此处解答 *) Admitted.
(** [] *)

Theorem merge_priq:  forall p q, priq p -> priq q -> priq (merge p q).
Proof.
 intros. unfold merge. apply join_valid; auto.
Qed.

(** **** 练习：5 星, standard, optional (delete_max_Some_priq)  *)
Theorem delete_max_Some_priq:
      forall p q k, priq p -> delete_max p = Some(k,q) -> priq q.
(* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** The Abstraction Relation *)

(** [tree_elems t l]    means that the keys in t are the same as the
   elements of l (with repetition) *)

Inductive tree_elems: tree -> list key -> Prop :=
| tree_elems_leaf: tree_elems Leaf nil
| tree_elems_node:  forall bl br v tl tr b,
           tree_elems tl bl ->
           tree_elems tr br ->
           Permutation b (v::bl++br) ->
           tree_elems (Node v tl tr) b.

(** **** 练习：3 星, standard (priqueue_elems)  

    Make an inductive definition, similar to [tree_elems], to relate
  a priority queue  "l"  to a list of all its elements.

  As you can see in the definition of [tree_elems],  a [tree] relates to
  _any_ permutation of its keys, not just a single permutation.
  You should make your [priqueue_elems] relation behave similarly,
  using (basically) the same technique as in [tree_elems].
*)

Inductive priqueue_elems: list tree -> list key -> Prop :=
             (* 请在此处解答 *)
.
(* 请勿修改下面这一行： *)
Definition manual_grade_for_priqueue_elems : option (nat*string) := None.
(** [] *)

Definition Abs (p: priqueue) (al: list key) := priqueue_elems p al.

(* ================================================================= *)
(** ** Sanity Checks on the Abstraction Relation *)

(** **** 练习：2 星, standard (tree_elems_ext)  

    Extensionality theorem for the tree_elems relation *)

Theorem tree_elems_ext: forall t e1 e2,
  Permutation e1 e2 -> tree_elems t e1 -> tree_elems t e2.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (tree_perm)  *)
Theorem tree_perm: forall t e1 e2,
  tree_elems t e1 -> tree_elems t e2 -> Permutation e1 e2.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (priqueue_elems_ext)  

    To prove [priqueue_elems_ext], you should almost be able to cut-and-paste the
   proof of [tree_elems_ext], with just a few edits.  *)

Theorem priqueue_elems_ext: forall q e1 e2,
  Permutation e1 e2 -> priqueue_elems q e1 -> priqueue_elems q e2.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (abs_perm)  *)
Theorem abs_perm: forall p al bl,
   priq p -> Abs p al -> Abs p bl -> Permutation al bl.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard (can_relate)  *)
Lemma tree_can_relate: forall t, exists al, tree_elems t al.
Proof.
(* 请在此处解答 *) Admitted.

Theorem can_relate:  forall p, priq p -> exists al, Abs p al.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Various Functions Preserve the Abstraction Relation *)
(** **** 练习：1 星, standard (empty_relate)  *)
Theorem empty_relate:  Abs empty nil.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (smash_elems)  

     Warning:  This proof is rather long. *)

Theorem smash_elems: forall n t u bt bu,
                     pow2heap n t -> pow2heap n u ->
                     tree_elems t bt -> tree_elems u bu ->
                     tree_elems (smash t u) (bt ++ bu).
(* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Optional Exercises *)

(**  Some of these proofs are quite long, but they're not especially tricky. *)

(** **** 练习：4 星, standard, optional (carry_elems)  *)
Theorem carry_elems:
      forall n q,  priq' n q ->
      forall t, (t=Leaf \/ pow2heap n t) ->
      forall eq et, priqueue_elems q eq ->
                          tree_elems t et ->
                          priqueue_elems (carry q t) (eq++et).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (insert_elems)  *)
Theorem insert_relate:
        forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：4 星, standard, optional (join_elems)  *)
Theorem join_elems:
                forall p q c n,
                      priq' n p ->
                      priq' n q ->
                      (c=Leaf \/ pow2heap n c) ->
                  forall pe qe ce,
                             priqueue_elems p pe ->
                             priqueue_elems q qe ->
                             tree_elems c ce ->
                              priqueue_elems (join p q c) (ce++pe++qe).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：2 星, standard, optional (merge_relate)  *)
Theorem merge_relate:
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       Permutation al (pl++ql).
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, standard, optional (delete_max_None_relate)  *)
Theorem delete_max_None_relate:
        forall p, priq p -> (Abs p nil <-> delete_max p = None).
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, standard, optional (delete_max_Some_relate)  *)
Theorem delete_max_Some_relate:
  forall (p q: priqueue) k (pl ql: list key), priq p ->
   Abs p pl ->
   delete_max p = Some (k,q) ->
   Abs q ql ->
   Permutation pl (k::ql) /\ Forall (ge k) ql.
(* 请在此处解答 *) Admitted.
(** [] *)

(** With the following line, we're done!  We have demonstrated that
  Binomial Queues are a correct implementation of mergeable
  priority queues.  That is, we have exhibited a [Module BinomQueue]
  that satisfies the [Module Type PRIQUEUE]. *)

End BinomQueue.

(* ################################################################# *)
(** * Measurement. *)

(** **** 练习：5 星, standard, optional (binom_measurement)  

    Adapt the program (but not necessarily the proof) to use Ocaml integers
  as keys, in the style shown in [Extract].   Write an ML program to
  exercise it with random inputs.  Compare the runtime to the implementation
  from [Priqueue], also adapted for Ocaml integers.

    [] *)

(* Sat Jan 26 15:18:06 UTC 2019 *)
