(** * Inductively Defined Propositions *)

From LF  Require Export Logic.



(** We've seen several ways of constructing propositions.

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal, e.g. [x + y = y + x].

       - We can combine propositions using implication and
         quantification (and the other logical operators).

Now  we define a new proposition primitively using [Inductive].
*)


(**  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.

    More precisely, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful].
       - Rule [b_5]: The number [5] is [beautiful].
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(* ================================================================= *)
(** ** Inference Rules *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)

(**

                              -----------                               (b_0)
                              beautiful 0

                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion hold unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_:

         ----------- (b_3)   ----------- (b_5)
         beautiful 3       beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8
*)
(**
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:


         ----------- (b_5)   ----------- (b_3)
         beautiful 5       beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8
*)

(** **** Exercise: 1 star, standard (varieties_of_beauty)

    How many different ways are there to show that [8] is [beautiful]? *)

(* FILL IN HERE

    [] *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
|  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).



(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.
*)

(** Compare with previous use of [Inductive]

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.


Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.



    The rules introduced this way have the same status as proven
    theorems.  So we can use Coq's [apply] tactic with the rule names
    to prove that particular numbers are [beautiful].  *)

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
 (** You can use [constructor] instead of [apply c_i] but beware
 that they are used in chronological order. So, this is always safe
 when the constructors do not overlap. Otherwise you can say [constructor i] for
the _i-th_ constructor.*)
   Restart.
   apply b_sum with (n:=3) (m:=5).
   constructor.
   constructor.
Qed.
(** One cannot use [eapply] (nor [econstrictor]) immediately, as it would require
_e-unification_, that is the question: are there x,y such that 8 = x +
y?  This is in general undecidable.

We could use the [change] tactic:

change 8 with (3 + 5).
eapply b_sum.

but this means solving the equation ourselves, so what's the difference.
*)



(** We can also instruct Coq to apply the constructors automatically as
safe introduction rule of the [auto] tactic. We'll
see about that later on.*)

(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  assumption.
Qed.

(** **** Exercise: 1 star, standard (b_times2) *)
Search (?X + 0 = ?X).

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n H. simpl. rewrite plus_0_r.
  apply b_sum with (n := n) (m := n).
  - assumption.
  - assumption.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (b_timesm)

    HINT: by _induction_ on [m] *)

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m H. induction m as [| m' IH].
  - simpl. apply b_0.
  - simpl. apply b_sum with (n := n) (m := m' * n).
    + assumption.
    + assumption.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Induction Over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)



(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactics that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_. We will introduce
    a new tactic, [inversion], which generalizes [destruct]. *)
  (**  To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

  (** This yields the following induction principle:

  [gorgeous_ind : forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, gorgeous n -> P n -> P (3 + n)) ->
    (forall n : nat, gorgeous n -> P n -> P (5 + n)) ->
    forall n : nat, gorgeous n -> P n]

      As a rule:



      P 0 (gorgeous n -> P n -> P (3 + n))  (gorgeous n -> P n -> P (5 + n))
      ------------------------------------------------------------------------                 (g_ind)
                  forall m : nat, gorgeous m -> P m

*)

        (** **** Exercise: 1 star, standard (gorgeous_tree)

    Write out the definition of [gorgeous] numbers using inference rule
    notation.

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 1 star, standard (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H.
  apply g_plus5 in H.
  apply g_plus5 in H.
  apply g_plus3 in H.
  assumption.
Qed.

(** [] *)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this, first the LtR direction: *)


Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
  (* WORKED IN CLASS *)
   intros n H.
   induction H as [|n'|n'].
   (*Case "g_0". *)
       - apply b_0.
   (* Case "g_plus3". *)
       - apply b_sum.
         + apply b_3.
         + apply IHgorgeous.
   (* Case "g_plus5". *)
       - apply b_sum.
         + apply b_5.
         + apply IHgorgeous.
Qed.

(** Notice that the argument proceeds by induction on the _evidence_ [H]! *)

(** Since inductively defined proof objects are often called
    "derivation trees," this form of proof is also known as _induction
    on derivations_.

    _Template_:

       - _Theorem_: <Proposition of the form "[Q -> P]," where [Q] is
         some inductively defined proposition (more generally,
         "For all [x] [y] [z], [Q x y z -> P x y z]")>

         _Proof_: By induction on a derivation of [Q].  <Or, more
         generally, "Suppose we are given [x], [y], and [z].  We
         show that [Q x y z] implies [P x y z], by induction on a
         derivation of [Q x y z]"...>

           <one case for each constructor [c] of [Q]...>

           - Suppose the final rule used to show [Q] is [c].  Then
             <...and here we state the types of all of the [a]'s
             together with any equalities that follow from the
             definition of the constructor and the IH for each of
             the [a]'s that has type [Q], if there are any>.  We must
             show <...and here we restate [P]>.

             <go on and prove [P] to finish the case...>

           - <other cases similarly...>                        []

*)

(** For the other direction, see exercise [beautiful_gorgeous]*)

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   (* Case "n = 0". *)
  - apply b_0.
   (* Case "n = S n'" We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers.
 This is given precisely by the shape of the
    constructors for [gorgeous]. *)



(** **** Exercise: 2 stars, standard (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [| n' Hn' IHn' | n' Hn' IHn'].
  - simpl. assumption.
  - apply g_plus3 in IHn'. assumption.
  - apply g_plus5 in IHn'. assumption.
Restart.
  intros n m Hn Hm. induction Hn as [| n' Hn' IH | n' Hn' IH].
  - simpl. assumption.
  - apply g_plus3 with (n := n' + m). assumption.
  - apply g_plus5 with (n := n' + m). assumption.
Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H. induction H as [| | | n' m' Hn' IHn' Hm' IHm'].
  - apply g_0.
  - apply g_plus3. apply g_0.
  - apply g_plus5. apply g_0.
  - apply gorgeous_sum.
    + assumption.
    + assumption.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (g_times2)

    Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros x y z.
  rewrite plus_comm with z x.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
  intros n H.
  simpl. rewrite plus_0_r.
  induction H as [| n' H' IH | n' H' IH].
  - simpl. apply g_0.
  - apply g_plus3 in IH. apply g_plus3 in IH.
    rewrite helper_g_times2.
    assumption.
  - apply g_plus5 in IH. apply g_plus5 in IH.
    rewrite helper_g_times2.
    assumption.
Qed.

(** [] *)



(* ================================================================= *)
(** ** [Inversion] on Evidence *)


(** In previous chapters  we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if this is the case. *)

Fixpoint evenb (n:nat)  :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Check  evenb.
(* evenb : nat -> bool *)

Goal evenb 8 = true.
Proof. reflexivity. Qed.

(** An alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** We're going to appreciate the relative merits in the next lectures:
suffices to say that the relational way is more general, as it does not
have to deal with _termination_, nor with _totality_. *)

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)

(**  Again, the type of [ev], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[ev] is a _function_ from numbers to
    propositions," (2) "[ev] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[ev] is a _property_ of numbers."  *)


(** A simple lemma requiring induction. *)

Theorem ev_even: forall n ,  ev n -> evenb n = true.
Proof.
intros.
induction H.
(* Case "ev_0". *)
 - reflexivity.
(* Case "ev_s". *)
 - simpl. assumption.
Qed.

(** INVERSION: Suppose we are proving some fact involving a number [n], and we
    are given [ev n] as a hypothesis.
    By the definition of [ev], there are two cases to consider:

    - If the evidence is of the form [ev_0], we know that [n = 0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n']. *)

(** We can perform this kind of reasoning in Coq, again using
    the [inversion] tactic.  Besides allowing us to reason about
    equalities involving constructors, [inversion] provides a
    case-analysis principle for inductively defined propositions.
    When used in this way, its syntax is similar to [destruct]: We
    pass it a list of identifiers separated by [|] characters to name
    the arguments to each of the possible constructors.  *)

(** Here's an example of [inversion] at work:*)
Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(**

    - If the evidence is of the form [ev_0], we know that [n = 0].
      Therefore, it suffices to show that [ev (pred (pred 0))] holds.
      By the definition of [pred], this is equivalent to showing that
      [ev 0] holds, which directly follows from [ev_0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n'].  We must then
      show that [ev (pred (pred (S (S n'))))] holds, which, after
      simplification, follows directly from [E']. *)

(** Another example, where we invert on a predicate over a term, not a parameter:*)
Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E. assumption.
 Qed.

(** By using [inversion], we can also apply the principle of explosion
    to "obviously contradictory" hypotheses involving inductive
    properties. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.


(** **** Exercise: 1 star, standard, optional

    What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* FILL IN HERE

    [] *)


(* ================================================================= *)
(** ** [inversion] recap *)

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)

(** **** Exercise: 1 star, standard (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [| n' H1 H2].
  inversion H1 as [| n'' H3 H4].
  assumption.
Qed.

(** An example on how [inversion] tactic can  be iteratively used by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : forall (Q : Prop),  ev 5 ->  Q.
Proof.
  (* WORKED IN CLASS *)
  intros Q E. inversion E as [| n' E'].
  inversion E' as [| n'' E''].
  inversion E''.
  (* Contradiction, as neither constructor can possibly apply... *)  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially usefulA (ev_ev__ev)

    Careful on what you induct on *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn. induction Hn as [| n' Hn' IH].
  - simpl in Hnm. assumption.
  - apply IH.
    simpl in Hnm.
    inversion Hnm as [| n'' H1 H2].
    assumption.
Qed.

(** [] *)

(* ################################################################# *)
(** * Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.

(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** Note that in the online version of the book, this is
written in an alternative functional way, in lieu of implication.
It's just style, but it lets you name the subderivation  [H]. *)

Inductive led : nat -> nat -> Prop :=
  | le_nd (n :nat) : led n n
  | le_Sd (n m : nat) (H : led n m) : led n (S m).

Print led.
(* Inductive led : nat -> nat -> Prop :=
    le_nd : forall n : nat, led n n
  | le_Sd : forall n m : nat,
            led n m ->
            led n (S m)*)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties.  We
    can [apply] the constructors to prove [<=] goals (e.g., to show
    that [3<=3] or [3<=6]), and we can use tactics like [inversion] to
    extract information from [<=] hypotheses in the context (e.g., to
    prove that [(2 <= 1) -> 2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Goal
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
 repeat constructor. Qed.

Goal
  forall (Q : Prop), (2 <= 1) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P H. inversion H. inversion H2.  Qed.

End LeModule.



(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).


(** Note that in the above definition of [le], the argument [n] does
_not_ change.  So we can write [<=],  making [n] a
_parameter_ of the definition, which thus  needs _not_ be quantified
over the constructors: *)

Inductive le'  (n : nat)  : nat -> Prop :=
  | le'_n :  le' n n
  | le'_S : forall  m, (le' n m) -> (le' n (S m)).

(**  Recall: [n] is a
_parameter_ of the definition, while whatever occurs after the ":" is an _index_.

Try to make this distinction when writing a relation -- It also gives a better induction principle.
 *)

(** The two versions are obviously equivalent: here's one direction: *)

Theorem lel : forall n m, le n m -> le' n m.
intros. induction H.
  - constructor.
  - constructor. assumption. Qed.

(** However, making _all_ arguments parameters does not work, because the second argument needs to vary in the first and second clause:*)

Fail Inductive le''  (n m : nat)  :  Prop :=
  | le''_n :  le'' n n
  | le''_S :  (le'' n m) -> (le'' n (S m)).

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of the
    connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Coq; all the others are defined inductively.  We'll see these
    definitions in this section. *)

Module Props.

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for [P
    /\ Q] as consisting of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] and [intros]
    patterns can be used on a conjunctive hypothesis.  Case analysis
    allows us to consider all possible ways in which [P /\ Q] was
    proved -- here just one (the [conj] constructor).

    Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor, here [conj].  In particular,
    it works for [and] and it's an abbreviation for applying the constructor: *)
Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  (* alias [apply conj]*)
  - intros. destruct H as [HP HQ]. apply conj.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. apply conj.
    + apply HP.
    + apply HQ.
Qed.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.
(* ================================================================= *)
(** ** Disjunction *)

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct: *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. [left/right] are
again just an [apply] of the constrctors.

     *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

(** The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x]. *)

(** The more familiar form [exists x, P x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

Definition e1 := ex (fun n => ev n) : Prop.
Goal e1.
unfold e1.
apply (ex_intro (fun x => ev x) 0).
constructor.
Qed.
(* ================================================================= *)
(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  | I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop := .

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. *)

(* ################################################################# *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has the
    following inductive definition.  (Actually, the definition in the
    standard library is a slight variant of this, which gives an
    induction principle that is slightly easier to use.) *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(** The way to think about this definition is that, given a set [X],
    it defines a _family_ of propositions "[x] is equal to [y],"
    indexed by pairs of values ([x] and [y]) from [X].  There is just
    one way of constructing evidence for members of this family:
    applying the constructor [eq_refl] to a type [X] and a single
    value [x : X], which yields evidence that [x] is equal to [x].

    Other types of the form [eq x y] where [x] and [y] are not the
    same are thus uninhabited. *)

(** We can use [eq_refl] to construct evidence that, for example, [2 =
    2].  Can we also use it to construct evidence that [1 + 1 = 2]?
    Yes, we can.  Indeed, it is the very same piece of evidence!

    The reason is that Coq treats as "the same" any two terms that are
    _convertible_ according to a  set of computation rules.

    These rules, which are similar to those used by [Compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.  *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.



(** **** Exercise: 2 stars, standard (equality__leibniz_equality)

    The inductive definition of equality implies _Leibniz equality_:
    what we mean when we say "[x] and [y] are equal" is that every
    property on [P] that is true of [x] is also true of [y].  *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
  intros X x y H1 P H2. destruct H1. assumption.
Qed.

(** [] *)

(** **** Exercise: 5 stars, standard, optional (leibniz_equality__equality)

    Show that, in fact, the inductive definition of equality is
    _equivalent_ to Leibniz equality: *)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros X x y H. apply H. apply eq_refl.
Qed.

(** [] *)

End MyEquality.
End Props.





(** Here are a few more simple relations on numbers/lists: *)

Inductive square_of (n:nat) :  nat -> Prop :=
  sq : square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive last (x : nat) : (list nat) -> Prop :=
 | xl : last x [x]
 | xs : forall y xs, last x xs ->  last x (y::xs).

Inductive lastp {X : Type} (x : X) : (list X) -> Prop :=
 | x1 : lastp x [x]
 | x2 : forall y xs, lastp x xs ->  lastp x (y::xs).

Goal  lastp 3 [1;2;3].
Proof.
  apply x2. apply x2. apply x1.
Qed.

Goal   ~ lastp 3 [1;2].
Proof.
(* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, standard, especially useful (total_relation)

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Definition total_relation (n m : nat) := n <= m \/ m <= n.

(** **** Exercise: 2 stars, standard (empty_relation)

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Definition empty_relation (n m : nat) := n < m /\ m < n.

(** **** Exercise: 2 stars, standard, optional (le_exercises)

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno. induction Hno as [| o' Hno' IH].
  - assumption.
  - apply le_S. assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n' IH].
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H as [| m' H' IH].
  - apply le_n.
  - apply le_S. assumption.
Restart.
  (* Search (?X <= S ?X). *)
  intros n m H. induction H as [| m' H' IH].
  - reflexivity.
  - rewrite IH. apply PeanoNat.Nat.le_succ_diag_r.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. induction m as [| m' IH].
  - inversion H as [H0 | zero H1 H2].
    + apply le_n.
    + inversion H1.
  - inversion H as [H0 | Sm H1 H2].
    + apply le_n.
    + apply le_S. apply IH. assumption.
Restart.
  intros n m H. inversion H as [H1 | m' H1 H2].
  - apply le_n.
  - rewrite <- H1. apply le_S. apply le_n.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b as [| b' IH].
  - rewrite plus_0_r. apply le_n.
  - rewrite plus_n_Sm. apply le_S. assumption.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  inversion H as [H1 | n' H1 H2].
  - split.
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
  - split.
    + destruct H1 as [| m' H1'] eqn:E.
      * rewrite H2. rewrite <- H.
        apply n_le_m__Sn_le_Sm. apply le_plus_l.
      * rewrite H2. rewrite <- H.
        apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + destruct H1 as [| m' H1'] eqn:E.
      * rewrite H2. rewrite <- H.
        apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
      * rewrite H2. rewrite <- H.
        apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros n m H. apply le_S. assumption.
Qed.

Theorem leb_true : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n as [| n' IH].
  - intros m H. apply O_le_n.
  - intros m H. destruct m as [| m'] eqn:E.
    + discriminate H.
    + simpl in H. apply IH in H.
      apply n_le_m__Sn_le_Sm. assumption.
Qed.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. assumption.
Qed.

(* Hint: This may be easiest to prove by induction on [m]. *)
Theorem le_leb : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IH].
  - intros n H. inversion H. reflexivity.
  - intros n H. destruct n as [| n'] eqn:E.
    + simpl. reflexivity.
    + simpl. apply Sn_le_Sm__n_le_m in H. apply IH. assumption.
Qed.

(* Hint: This theorem can be easily proved without using [induction]. *)
Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o Hnm Hmo.
  apply leb_true in Hnm.
  apply leb_true in Hmo.
  apply le_leb.
  apply le_trans with m.
  - assumption.
  - assumption.
Qed.

(** **** Exercise: 2 stars, standard, optional (leb_false) *)
Theorem leb_false : forall n m,
  leb n m = false -> ~(n <= m).
Proof.
  unfold not.
  intros n m H1 H2.
  apply le_leb in H2.
  rewrite H2 in H1.
  discriminate H1.
Qed.

(** [] *)





(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

    [1,2,3]

    is a subsequence of each of the lists

    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]

    but it is _not_ a subsequence of any of the lists

    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

(* FILL IN HERE *)

(** **** Exercise: 1 star, standard (double_even) *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use nat induction to prove these simple facts about [double]: *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
(** **** Exercise: 3 stars, standard, optional (ev_plus_plus) *)

(* 2023-10-19 12:33 *)
