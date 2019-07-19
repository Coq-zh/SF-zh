(** * Sub: Subtyping *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.

(* ################################################################# *)
(** * Concepts *)

(** We now turn to the study of _subtyping_, a key feature
    needed to support the object-oriented programming style. *)

(* ================================================================= *)
(** ** A Motivating Example *)

(** Suppose we are writing a program involving two record types
    defined as follows:

      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
*)

(** In the simply typed lamdba-calculus with records, the term

      (\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1}

   is not typable, since it applies a function that wants a two-field
   record to an argument that actually provides three fields, while the
   [T_App] rule demands that the domain type of the function being
   applied must match the type of the argument precisely.

   But this is silly: we're passing the function a _better_ argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument [r] is project the field [age]
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra [gpa] field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an [age] field.

   More generally, a record with more fields is "at least as good in
   any context" as one with just a subset of these fields, in the
   sense that any value belonging to the longer record type can be
   used _safely_ in any context expecting the shorter record type.  If
   the context expects something with the shorter type but we actually
   give it something with the longer type, nothing bad will
   happen (formally, the program will not get stuck).

   The principle at work here is called _subtyping_.  We say that "[S]
   is a subtype of [T]", written [S <: T], if a value of type [S] can
   safely be used in any context where a value of type [T] is
   expected.  The idea of subtyping applies not only to records, but
   to all of the type constructors in the language -- functions,
   pairs, etc. *)

(** Safe substitution principle:

       - [S] is a subtype of [T], written [S <: T], if a value of type
         [S] can safely be used in any context where a value of type
         [T] is expected.
*)

(* ================================================================= *)
(** ** Subtyping and Object-Oriented Languages *)

(** Subtyping plays a fundamental role in many programming
    languages -- in particular, it is closely related to the notion of
    _subclassing_ in object-oriented languages.

    An _object_ in Java, C[#], etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method [m] of an object [o] on some arguments [a1..an]
    roughly consists of projecting out the [m] field of [o] and
    applying it to [a1..an].

    The type of an object is called a _class_ -- or, in some
    languages, an _interface_.  It describes which methods and which
    data fields the object offers.  Classes and interfaces are related
    by the _subclass_ and _subinterface_ relations.  An object
    belonging to a subclass (or subinterface) is required to provide
    all the methods and fields of one belonging to a superclass (or
    superinterface), plus possibly some more.

    The fact that an object from a subclass can be used in place of
    one from a superclass provides a degree of flexibility that is
    extremely handy for organizing complex libraries.  For example, a
    GUI toolkit like Java's Swing framework might define an abstract
    interface [Component] that collects together the common fields and
    methods of all objects having a graphical representation that can
    be displayed on the screen and interact with the user, such as the
    buttons, checkboxes, and scrollbars of a typical GUI.  A method
    that relies only on this common interface can now be applied to
    any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared [private].  Classes can give
    _initializers_ that are used when constructing objects.  Code in
    subclasses can cooperate with code in superclasses via
    _inheritance_.  Classes can have static methods and fields.  Etc.,
    etc.

    To keep things simple here, we won't deal with any of these
    issues -- in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in [Pierce 2002] (in Bib.v), if
    you are interested.)  Instead, we'll study the core concepts
    behind the subclass / subinterface relation in the simplified
    setting of the STLC. *)

(* ================================================================= *)
(** ** The Subsumption Rule *)

(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:

                         Gamma |- t \in S     S <: T
                         ---------------------------                    (T_Sub)
                               Gamma |- t \in T

    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *)

(** For example, we may know that [t] is a record with two
    fields (e.g., [S = {x:A->A, y:B->B}]), but choose to forget about
    one of the fields ([T = {y:B->B}]) so that we can pass [t] to a
    function that requires just a single-field record. *)

(* ================================================================= *)
(** ** The Subtype Relation *)

(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)

(* ----------------------------------------------------------------- *)
(** *** Structural Rules *)

(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is
    better (richer, safer) than [U] and [U] is better than [T],
    then [S] is better than [T]...

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

    ... and a rule of _reflexivity_, since certainly any type [T] is
    as good as itself:

                                   ------                              (S_Refl)
                                   T <: T
*)

(* ----------------------------------------------------------------- *)
(** *** Products *)

(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype
    of another if each of its components is.

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
*)

(* ----------------------------------------------------------------- *)
(** *** Arrows *)

(** The subtyping rule for arrows is a little less intuitive.
    Suppose we have functions [f] and [g] with these types:

       f : C -> Student
       g : (C->Person) -> D

    That is, [f] is a function that yields a record of type [Student],
    and [g] is a (higher-order) function that expects its argument to be
    a function yielding a record of type [Person].  Also suppose that
    [Student] is a subtype of [Person].  Then the application [g f] is
    safe even though their types do not match up precisely, because
    the only thing [g] can do with [f] is to apply it to some
    argument (of type [C]); the result will actually be a [Student],
    while [g] will be expecting a [Person], but this is safe because
    the only thing [g] can then do is to project out the two fields
    that it knows about ([name] and [age]), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:

                                  S2 <: T2
                              ----------------                     (S_Arrow_Co)
                            S1 -> S2 <: S1 -> T2

    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

    But notice that the argument types are subtypes "the other way round":
    in order to conclude that [S1->S2] to be a subtype of [T1->T2], it
    must be the case that [T1] is a subtype of [S1].  The arrow
    constructor is said to be _contravariant_ in its first argument
    and _covariant_ in its second.

    Here is an example that illustrates this:

       f : Person -> C
       g : (Student -> C) -> D

    The application [g f] is safe, because the only thing the body of
    [g] can do with [f] is to apply it to some argument of type
    [Student].  Since [f] requires records having (at least) the
    fields of a [Person], this will always work. So [Person -> C] is a
    subtype of [Student -> C] since [Student] is a subtype of
    [Person].

    The intuition is that, if we have a function [f] of type [S1->S2],
    then we know that [f] accepts elements of type [S1]; clearly, [f]
    will also accept elements of any subtype [T1] of [S1]. The type of
    [f] also tells us that it returns elements of type [S2]; we can
    also view these results belonging to any supertype [T2] of
    [S2]. That is, any function [f] of type [S1->S2] can also be
    viewed as having type [T1->T2]. *)

(* ----------------------------------------------------------------- *)
(** *** Records *)

(** What about subtyping for record types? *)

(** The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields [x] and [y], it is perfectly safe
    for it to receive a record with fields [x], [y], and [z]; the [z]
    field will simply be ignored.  For example,

    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}

    This is known as "width subtyping" for records. *)

(** We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field [x] of type [T], it will be happy with a record
    having a field [x] of type [S] as long as [S] is a subtype of
    [T]. For example,

    {x:Student} <: {x:Person}

    This is known as "depth subtyping". *)

(** Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,

    {name:String,age:Nat} <: {age:Nat,name:String}

    This is known as "permutation subtyping". *)

(** We _could_ formalize these requirements in a single subtyping rule
    for records as follows:

                        forall jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}

    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation.

    However, this rule is rather heavy and hard to read, so it is often
    decomposed into three simpler rules, which can be combined using
    [S_Trans] to achieve all the same effects. *)

(** First, adding fields to the end of a record type gives a subtype:

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

    We can use [S_RcdWidth] to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    [{age:Nat,name:String} <: {age:Nat}]. *)

(** Second, subtyping can be applied inside the components of a compound
    record type:

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

    For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
    show that [{y:Student, x:Nat} <: {y:Person}]. *)

(** Third, subtyping can reorder fields.  For example, we
    want [{name:String, gpa:Nat, age:Nat} <: Person].  (We
    haven't quite achieved this yet: using just [S_RcdDepth] and
    [S_RcdWidth] we can only drop fields from the _end_ of a record
    type.)  So we add:

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces).

    - In early versions of Java, a subclass could not change the
      argument or result types of a method of its superclass (i.e., no
      depth subtyping or no arrow subtyping, depending how you look at
      it). *)

(** **** 练习：2 星, standard, recommended (arrow_sub_wrong)  

    Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:

                            S1 <: T1    S2 <: T2
                            --------------------                (S_Arrow_wrong)
                            S1 -> S2 <: T1 -> T2

    Give a concrete example of functions [f] and [g] with the following
    types...

       f : Student -> Nat
       g : (Person -> Nat) -> Nat

    ... such that the application [g f] will get stuck during
    execution.  (Use informal syntax.  No need to prove formally that
    the application gets stuck.)

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_arrow_sub_wrong : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Top *)

(** Finally, it is convenient to give the subtype relation a maximum
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:

                                   --------                             (S_Top)
                                   S <: Top

    The [Top] type is an analog of the [Object] type in Java and C#. *)

(* ----------------------------------------------------------------- *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

    - adding a base type [Top],

    - adding the rule of subsumption

                         Gamma |- t \in S     S <: T
                         ---------------------------                    (T_Sub)
                               Gamma |- t \in T

      to the typing relation, and

    - defining a subtype relation as follows:

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(* ================================================================= *)
(** ** Exercises *)

(** **** 练习：1 星, standard, optional (subtype_instances_tf_1)  

    Suppose we have types [S], [T], [U], and [V] with [S <: T]
    and [U <: V].  Which of the following subtyping assertions
    are then true?  Write _true_ or _false_ after each one.
    ([A], [B], and [C] here are base types like [Bool], [Nat], etc.)

    - [T->S <: T->S]

    - [Top->U <: S->Top]

    - [(C->C) -> (A*B)  <:  (C->C) -> (Top*B)]

    - [T->T->U <: S->S->V]

    - [(T->T)->U <: (S->S)->V]

    - [((T->S)->T)->U <: ((S->T)->S)->V]

    - [S*V <: T*U]

    [] *)

(** **** 练习：2 星, standard (subtype_order)  

    The following types happen to form a linear order with respect to subtyping:
    - [Top]
    - [Top -> Student]
    - [Student -> Person]
    - [Student -> Top]
    - [Person -> Student]

Write these types in order from the most specific to the most general.

Where does the type [Top->Top->Student] fit into this order?
That is, state how [Top -> (Top -> Student)] compares with each
of the five types above. It may be unrelated to some of them.  
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_subtype_order : option (nat*string) := None.
(** [] *)

(** **** 练习：1 星, standard (subtype_instances_tf_2)  

    Which of the following statements are true?  Write _true_ or
    _false_ after each one.

      forall S T,
          S <: T  ->
          S->S   <:  T->T

      forall S,
           S <: A->A ->
           exists T,
              S = T->T  /\  T <: A

      forall S T1 T2,
           (S <: T1 -> T2) ->
           exists S1 S2,
              S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 

      exists S,
           S <: S->S 

      exists S,
           S->S <: S  

      forall S T1 T2,
           S <: T1*T2 ->
           exists S1 S2,
              S = S1*S2  /\  S1 <: T1  /\  S2 <: T2  
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_subtype_instances_tf_2 : option (nat*string) := None.
(** [] *)

(** **** 练习：1 星, standard (subtype_concepts_tf)  

    Which of the following statements are true, and which are false?
    - There exists a type that is a supertype of every other type.

    - There exists a type that is a subtype of every other type.

    - There exists a pair type that is a supertype of every other
      pair type.

    - There exists a pair type that is a subtype of every other
      pair type.

    - There exists an arrow type that is a supertype of every other
      arrow type.

    - There exists an arrow type that is a subtype of every other
      arrow type.

    - There is an infinite descending chain of distinct types in the
      subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a subtype of [Si].

    - There is an infinite _ascending_ chain of distinct types in
      the subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a supertype of [Si].

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_subtype_concepts_tf : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (proper_subtypes)  

    Is the following statement true or false?  Briefly explain your
    answer.  (Here [Base n] stands for a base type, where [n] is
    a string standing for the name of the base type.  See the
    Syntax section below.)

    forall T,
         ~(T = Bool \/ exists n, T = Base n) ->
         exists S,
            S <: T  /\  S <> T
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_proper_subtypes : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (small_large_1)  
   - What is the _smallest_ type [T] ("smallest" in the subtype
     relation) that makes the following assertion true?  (Assume we
     have [Unit] among the base types and [unit] as a constant of this
     type.)

       empty |- (\p:T*Top. p.fst) ((\z:A.z), unit) \in A->A

   - What is the _largest_ type [T] that makes the same assertion true?

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_small_large_1 : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (small_large_2)  
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       empty |- (\p:(A->A * B->B). p) ((\z:A.z), (\z:B.z)) \in T

   - What is the _largest_ type [T] that makes the same assertion true?

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_small_large_2 : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard, optional (small_large_3)  
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       a:A |- (\p:(A*T). (p.snd) (p.fst)) (a, \z:A.z) \in A

   - What is the _largest_ type [T] that makes the same assertion true?

    [] *)

(** **** 练习：2 星, standard (small_large_4)  
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       exists S,
         empty |- (\p:(A*T). (p.snd) (p.fst)) \in S

   - What is the _largest_ type [T] that makes the same
     assertion true?

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_small_large_4 : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (smallest_1)  

    What is the _smallest_ type [T] that makes the following
    assertion true?

      exists S t,
        empty |- (\x:T. x x) t \in S
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_smallest_1 : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, standard (smallest_2)  

    What is the _smallest_ type [T] that makes the following
    assertion true?

      empty |- (\x:Top. x) ((\z:A.z) , (\z:B.z)) \in T
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_smallest_2 : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, standard, optional (count_supertypes)  

    How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.)

    [] *)

(** **** 练习：2 星, standard (pair_permutation)  

    The subtyping rule for product types

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                               S1*S2 <: T1*T2

    intuitively corresponds to the "depth" subtyping rule for records.
    Extending the analogy, we might consider adding a "permutation" rule

                                   --------------
                                   T1*T2 <: T2*T1

    for products.  Is this a good idea? Briefly explain why or why not.

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_pair_permutation : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Formal Definitions *)

(** Most of the definitions needed to formalize what we've discussed
    above -- in particular, the syntax and operational semantics of
    the language -- are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new [Inductive] definition for the subtyping
    relation.  Let's first do the identical bits. *)

(* ================================================================= *)
(** ** Core Definitions *)

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

(** In the rest of the chapter, we formalize just base types,
    booleans, arrow types, [Unit], and [Top], omitting record types
    and leaving product types as an exercise.  For the sake of more
    interesting examples, we'll add an arbitrary set of base types
    like [String], [Float], etc.  (Since they are just for examples,
    we won't bother adding any operations over these base types, but
    we could easily do so.) *)

Inductive ty : Type :=
  | Top   : ty
  | Bool  : ty
  | Base  : string -> ty
  | Arrow : ty -> ty -> ty
  | Unit  : ty
.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm 
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | unit : tm 
.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** The definition of substitution remains exactly the same as for the
    pure STLC. *)

Fixpoint subst (x:string) (s:tm)  (t:tm) : tm :=
  match t with
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test (subst x s t1) (subst x s t2) (subst x s t3)
  | unit =>
      unit 
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Likewise the definitions of the [value] property and the [step]
    relation. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_true :
      value tru
  | v_false :
      value fls
  | v_unit :
      value unit
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1  t2')
  | ST_TestTrue : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(* ================================================================= *)
(** ** Subtyping *)

(** Now we come to the interesting part.  We begin by defining
    the subtyping relation and developing some of its important
    technical properties. *)

(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (Arrow S1 S2) <: (Arrow T1 T2)
where "T '<:' U" := (subtype T U).

(** Note that we don't need any special rules for base types ([Bool]
    and [Base]): they are automatically subtypes of themselves (by
    [S_Refl]) and [Top] (by [S_Top]), and that's all we want. *)

Hint Constructors subtype.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").

Notation String := (Base "String").
Notation Float := (Base "Float").
Notation Integer := (Base "Integer").

Example subtyping_example_0 :
  (Arrow C Bool) <: (Arrow C Top).
  (* C->Bool <: C->Top *)
Proof. auto. Qed.

(** **** 练习：2 星, standard, optional (subtyping_judgements)  

    (Leave this exercise [Admitted] until after you have finished adding product
    types to the language -- see exercise [products] -- at least up to 
    this point in the file).

    Recall that, in chapter [MoreStlc], the optional section
    "Encoding Records" describes how records can be encoded as pairs.
    Using this encoding, define pair types representing the following
    record types:

    Person := { name : String } 
    Student := { name : String ; gpa : Float } 
    Employee := { name : String ; ssn : Integer }
*)
Definition Person : ty
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Definition Student : ty
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Definition Employee : ty
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

(** Now use the definition of the subtype relation to prove the following: *)

Example sub_student_person :
  Student <: Person.
Proof.
(* 请在此处解答 *) Admitted.

Example sub_employee_person :
  Employee <: Person.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** The following facts are mostly easy to prove in Coq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! *)

(** **** 练习：1 星, standard, optional (subtyping_example_1)  *)
Example subtyping_example_1 :
  (Arrow Top Student) <: (Arrow (Arrow C C) Person).
  (* Top->Student <: (C->C)->Person *)
Proof with eauto.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：1 星, standard, optional (subtyping_example_2)  *)
Example subtyping_example_2 :
  (Arrow Top Person) <: (Arrow Person Top).
  (* Top->Person <: Person->Top *)
Proof with eauto.
  (* 请在此处解答 *) Admitted.
(** [] *)

End Examples.

(* ================================================================= *)
(** ** Typing *)

(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in Arrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- app t1 t2 \in T2
  | T_True : forall Gamma,
       Gamma |- tru \in Bool
  | T_False : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  (* New rule of subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(** The following hints help [auto] and [eauto] construct typing
    derivations.  They are only used in a few places, but they give
    a nice illustration of what [auto] can do with a bit more 
    programming.  See chapter [UseAuto] for more on hints. *)

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

Module Examples2.
Import Examples.

(** Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Coq and prove it. *)

(** **** 练习：1 星, standard, optional (typing_example_0)  *)
(* empty |- ((\z:A.z), (\z:B.z))
         \in (A->A * B->B) *)
(* 请在此处解答 

    [] *)

(** **** 练习：2 星, standard, optional (typing_example_1)  *)
(* empty |- (\x:(Top * B->B). x.snd) ((\z:A.z), (\z:B.z))
         \in B->B *)
(* 请在此处解答 

    [] *)

(** **** 练习：2 星, standard, optional (typing_example_2)  *)
(* empty |- (\z:(C->C)->(Top * B->B). (z (\x:C.x)).snd)
              (\z:C->C. ((\z:A.z), (\z:B.z)))
         \in B->B *)
(* 请在此处解答 

    [] *)

End Examples2.

(* ################################################################# *)
(** * Properties *)

(** The fundamental properties of the system that we want to
    check are the same as always: progress and preservation.  Unlike
    the extension of the STLC with references (chapter [References]),
    we don't need to change the _statements_ of these properties to
    take subtyping into account.  However, their proofs do become a
    little bit more involved. *)

(* ================================================================= *)
(** ** Inversion Lemmas for Subtyping *)

(** Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:
       - [Bool] is the only subtype of [Bool], and
       - every subtype of an arrow type is itself an arrow type. *)

(** These are called _inversion lemmas_ because they play a
    similar role in proofs as the built-in [inversion] tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement [S <: T] and some constraints on the shape of [S] and/or
    [T], each inversion lemma reasons about what this derivation must
    look like to tell us something further about the shapes of [S] and
    [T] and the existence of subtype relations between their parts. *)

(** **** 练习：2 星, standard, optional (sub_inversion_Bool)  *)
Lemma sub_inversion_Bool : forall U,
     U <: Bool ->
     U = Bool.
Proof with auto.
  intros U Hs.
  remember Bool as V.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：3 星, standard (sub_inversion_arrow)  *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: Arrow V1 V2 ->
     exists U1 U2,
     U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  (* 请在此处解答 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Canonical Forms *)

(** The proof of the progress theorem -- that a well-typed
    non-value can always take a step -- doesn't need to change too
    much: we just need one small refinement.  When we're considering
    the case where the term in question is an application [t1 t2]
    where both [t1] and [t2] are values, we need to know that [t1] has
    the _form_ of a lambda-abstraction, so that we can apply the
    [ST_AppAbs] reduction rule.  In the ordinary STLC, this is
    obvious: we know that [t1] has a function type [T11->T12], and
    there is only one rule that can be used to give a function type to
    a value -- rule [T_Abs] -- and the form of the conclusion of this
    rule forces [t1] to be an abstraction.

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show [Gamma
    |- t1 \in T11->T12] is subsumption, then there is some
    _sub_-derivation whose subject is also [t1], and we can reason by
    induction until we finally bottom out at a use of [T_Abs].

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e., values) of function
    type. *)

(** **** 练习：3 星, standard, optional (canonical_forms_of_arrow_types)  *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in Arrow T1 T2 ->
  value s ->
  exists x S1 s2,
     s = abs x S1 s2.
Proof with eauto.
  (* 请在此处解答 *) Admitted.
(** [] *)

(** Similarly, the canonical forms of type [Bool] are the constants
    [tru] and [fls]. *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tru \/ s = fls.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember Bool as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The proof of progress now proceeds just like the one for the
    pure STLC, except that in several places we invoke canonical forms
    lemmas... *)

(** _Theorem_ (Progress): For any term [t] and type [T], if [empty |-
    t \in T] then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given, with [empty |- t \in T].  Proceed
    by induction on the typing derivation.

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [tru], and [fls] are
    already values.  The [T_Var] case is vacuous because variables
    cannot be typed in the empty context.  The remaining cases are
    more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |- t1 \in T1 -> T2], and [empty |-
      t2 \in T1].  Moreover, by the induction hypothesis, either [t1] is
      a value or it steps, and either [t2] is a value or it steps.
      There are three possibilities to consider:

      - Suppose [t1 --> t1'] for some term [t1'].  Then [t1 t2 --> t1' t2]
        by [ST_App1].

      - Suppose [t1] is a value and [t2 --> t2'] for some term [t2'].
        Then [t1 t2 --> t1 t2'] by rule [ST_App2] because [t1] is a
        value.

      - Finally, suppose [t1] and [t2] are both values.  By the
        canonical forms lemma for arrow types, we know that [t1] has the
        form [\x:S1.s2] for some [x], [S1], and [s2].  But then
        [(\x:S1.s2) t2 --> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_Test], then there
      are terms [t1], [t2], and [t3] such that [t = test t1 then t2 else
      t3], with [empty |- t1 \in Bool] and with [empty |- t2 \in T] and
      [empty |- t3 \in T].  Moreover, by the induction hypothesis,
      either [t1] is a value or it steps.

       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = tru] or [t1 = fls].  In either
         case, [t] can step, using rule [ST_TestTrue] or [ST_TestFalse].

       - If [t1] can step, then so can [t], by rule [ST_Test].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [S] such that [S <: T] and [empty |- t \in S].  The desired
      result is exactly the induction hypothesis for the typing
      subderivation.

    Formally: *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  - (* T_Var *)
    inversion H.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    + (* t1 steps *)
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  - (* T_Test *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + assert (t1 = tru \/ t1 = fls)
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
    + inversion H. rename x into t1'. eauto. 
Qed.

(* ================================================================= *)
(** ** Inversion Lemmas for Typing *)

(** The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are immediate from
    the definition in the pure STLC (formally: that can be obtained
    directly from the [inversion] tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same [has_type] statement.

    The following inversion lemma tells us that, if we have a
    derivation of some typing statement [Gamma |- \x:S1.t2 \in T] whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body [t2]. *)

(** _Lemma_: If [Gamma |- \x:S1.t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |- t2 \in S2] and [S1 -> S2 <: T].

    (Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!)

    _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |-
     \x:S1.t2 \in T].  Cases [T_Var], [T_App], are vacuous as those
     rules cannot be used to give a type to a syntactic abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [x:S1;
       Gamma |- t2 \in T12].  Picking [T12] for [S2] gives us what we
       need: [S1 -> T12 <: S1 -> T12] follows from [S_Refl].

     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |- \x:S1.t2
       \in S].  The IH for the typing subderivation tells us that there
       is some type [S2] with [S1 -> S2 <: S] and [x:S1; Gamma |- t2
       \in S2].  Picking type [S2] gives us what we need, since [S1 ->
       S2 <: T] then follows by [S_Trans].

    Formally: *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- (abs x S1 t2) \in T ->
     exists S2,
       Arrow S1 S2 <: T
       /\ (x |-> S1 ; Gamma) |- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (abs x S1 t2) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T12...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

(** Similarly... *)

Lemma typing_inversion_var : forall Gamma x T,
  Gamma |- (var x) \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (var x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Var *)
    exists T...
  - (* T_Sub *)
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- (app t1 t2) \in T2 ->
  exists T1,
    Gamma |- t1 \in (Arrow T1 T2) /\
    Gamma |- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (app t1 t2) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_App *)
    exists T1...
  - (* T_Sub *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true : forall Gamma T,
  Gamma |- tru \in T ->
  Bool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tru as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : forall Gamma T,
  Gamma |- fls \in T ->
  Bool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember fls as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
  Gamma |- (test t1 t2 t3) \in T ->
  Gamma |- t1 \in Bool
  /\ Gamma |- t2 \in T
  /\ Gamma |- t3 \in T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (test t1 t2 t3) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Test *)
    auto.
  - (* T_Sub *)
    destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |- unit \in T ->
    Unit <: T.
Proof with eauto.
  intros Gamma T Htyp. remember unit as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- (abs x S1 s2) \in (Arrow T1 T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...  Qed.

(* ================================================================= *)
(** ** Context Invariance *)

(** The context invariance lemma follows the same pattern as in the
    pure STLC. *)

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
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test t1 t2 t3)
.

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
    apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold update, t_update. destruct (eqb_stringP x x0)...
  - (* T_Test *)
    apply T_Test... 
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp;
      subst; inversion Hafi; subst...
  - (* T_Abs *)
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    unfold update, t_update in Hctx.
    rewrite <- eqb_string_false_iff in H2.
    rewrite H2 in Hctx... Qed.

(* ================================================================= *)
(** ** Substitution *)

(** The _substitution lemma_ is proved along the same lines as
    for the pure STLC.  The only significant change is that there are
    several places where, instead of the built-in [inversion] tactic,
    we need to use the inversion lemmas that we proved above to
    extract structural information from assumptions about the
    well-typedness of subterms. *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (x |-> U ; Gamma) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  - (* var *)
    rename s into y.
    destruct (typing_inversion_var _ _ _ Htypt)
        as [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; eauto;
    subst.
    inversion Hctx; subst. clear Hctx.
    apply context_invariance with empty...
    intros x Hcontra.
    destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
    inversion HT'.
  - (* app *)
    destruct (typing_inversion_app _ _ _ _ Htypt)
        as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  - (* abs *)
    rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (Arrow T1 T2)... apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst.
      rewrite <- eqb_string_false_iff in Hxy. rewrite Hxy...
  - (* tru *)
      assert (Bool <: S)
        by apply (typing_inversion_true _ _  Htypt)...
  - (* fls *)
      assert (Bool <: S)
        by apply (typing_inversion_false _ _  Htypt)...
  - (* test *)
    assert  ((x |-> U ; Gamma) |- t1 \in Bool
         /\  (x |-> U ; Gamma) |- t2 \in S
         /\  (x |-> U ; Gamma) |- t3 \in S)
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto.
  - (* unit *)
    assert (Unit <: S)
      by apply (typing_inversion_unit _ _  Htypt)... 
Qed.

(* ================================================================= *)
(** ** Preservation *)

(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and again using inversion lemmas from above to extract structural
    information from typing assumptions. *)

(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |- t \in T] and [t --> t'], then [empty |- t' \in
    T].

    _Proof_: Let [t] and [T] be given such that [empty |- t \in T].  We
    proceed by induction on the structure of this typing derivation,
    leaving [t'] general.  The cases [T_Abs], [T_Unit], [T_True], and
    [T_False] cases are vacuous because abstractions and constants
    don't step.  Case [T_Var] is vacuous as well, since the context is
    empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that
       [t = t1 t2], [T = T2], [empty |- t1 \in T1 -> T2], and
       [empty |- t2 \in T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S.t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].

       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |- s2 \in T2].
       It then follows by the substitution lemma
       ([substitution_preserves_typing]) that [empty |- [x:=t2]
       t12 \in T2] as desired.

      - If the final step of the derivation uses rule [T_Test], then
        there are terms [t1], [t2], and [t3] such that [t = test t1 then
        t2 else t3], with [empty |- t1 \in Bool] and with [empty |- t2
        \in T] and [empty |- t3 \in T].  Moreover, by the induction
        hypothesis, if [t1] steps to [t1'] then [empty |- t1' : Bool].
        There are three cases to consider, depending on which rule was
        used to show [t --> t'].

           - If [t --> t'] by rule [ST_Test], then [t' = test t1' then t2
             else t3] with [t1 --> t1'].  By the induction hypothesis,
             [empty |- t1' \in Bool], and so [empty |- t' \in T] by
             [T_Test].

           - If [t --> t'] by rule [ST_TestTrue] or [ST_TestFalse], then
             either [t' = t2] or [t' = t3], and [empty |- t' \in T]
             follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |- t \in S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t --> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T... 
Qed.

(* ================================================================= *)
(** ** Records, via Products and Top *)

(** This formalization of the STLC with subtyping omits record
    types for brevity.  If we want to deal with them more seriously,
    we have two choices.

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    [RecordSub] shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and [Unit] types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    [Unit] as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use [Top].  So:

    {a:Nat, b:Nat} ----> {Nat,Nat}       i.e., (Nat,(Nat,Top))
    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e., (Nat,(Top,(Nat,Top)))

    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding. *)

(* ================================================================= *)
(** ** Exercises *)

(** **** 练习：2 星, standard (variations)  

    Each part of this problem suggests a different way of changing the
    definition of the STLC with Unit and subtyping.  (These changes
    are not cumulative: each part starts from the original language.)
    In each part, list which properties (Progress, Preservation, both,
    or neither) become false.  If a property becomes false, give a
    counterexample.

    - Suppose we add the following typing rule:

                           Gamma |- t \in S1->S2
                    S1 <: T1     T1 <: S1      S2 <: T2
                    -----------------------------------    (T_Funny1)
                           Gamma |- t \in T1->T2

    - Suppose we add the following reduction rule:

                             --------------------         (ST_Funny21)
                             unit --> (\x:Top. x)

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny3)
                               Unit <: Top->Top

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny4)
                               Top->Top <: Unit

    - Suppose we add the following reduction rule:

                             ---------------------      (ST_Funny5)
                             (unit t) --> (t unit)

    - Suppose we add the same reduction rule _and_ a new typing rule:

                             ---------------------       (ST_Funny5)
                             (unit t) --> (t unit)

                           --------------------------    (T_Funny6)
                           empty |- unit \in Top->Top

    - Suppose we _change_ the arrow subtyping rule to:

                          S1 <: T1 S2 <: T2
                          -----------------              (S_Arrow')
                          S1->S2 <: T1->T2

*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_variations : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Exercise: Adding Products *)

(** **** 练习：5 星, standard (products)  

    Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension by modifying the definitions and proofs above:

    - Add constructors for pairs, first and second projections,
      and product types to the definitions of [ty] and [tm], and
      extend the surrounding definitions accordingly
      (refer to chapter [MoreSTLC]):

        - value relation
        - substitution
        - operational semantics
        - typing relation

    - Extend the subtyping relation with this rule:

                        S1 <: T1    S2 <: T2
                        --------------------   (S_Prod)
                         S1 * S2 <: T1 * T2

    - Extend the proofs of progress, preservation, and all their
      supporting lemmas to deal with the new constructs.  (You'll also
      need to add a couple of completely new lemmas.) *)

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_products : option (nat*string) := None.
(** [] *)

(* Fri Jul 19 00:33:15 UTC 2019 *)
