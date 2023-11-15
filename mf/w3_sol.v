
(* 3.1
Prove the following logical principles without  automation: no auto, no tauto, no firstorder
*)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
  Proof.
  intros P Q Hpq Hqp neg.
  apply Hqp.
  apply Hpq.
  assumption.
  Restart (* forward *).
  intros P Q Hpq Hqp neg.
  apply Hpq in neg.
  apply Hqp in neg.
  exact neg.
  Restart.
  intros P Q Hpq Hqp neg.
  exact (Hqp (Hpq neg)).
Qed.

Theorem dist_exists_or : forall (A : Type) (P Q : A -> Prop),
            (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - intros H. destruct H. destruct H.
    + left. exists x. assumption.
    + right. exists x. assumption.
  - intros H. destruct H. destruct H.
    + exists x. left. assumption.
    + destruct H. exists x. right. assumption.
Qed.


(* the double negation principle requires the following classical axiom *)
Axiom excluded_middle : forall P : Prop,
  P \/ ~ P.

Theorem  dnn: forall P, ~~ P  -> P.
Proof.
  intros. destruct (excluded_middle P).
  - assumption.
  - apply H in H0. destruct H0.
Qed.

From Coq Require Export List.
  (* 3.2 State and prove the injectivity, disjointness and occur check property
for polymorphic List, similarly to what we did in class (Logic.v) for Nats.
 To get you started, here is the statement for disjointness*)

Print nil_cons.
Theorem  list_disj: forall (X :Type) (x  : X) (xs  : list X),
    ( nil <> (x :: xs)) .
Proof.

  intros X x xs contra.
      discriminate contra.
Qed.

Lemma list_ock: forall (X :Type) (x  : X) (xs  : list X),
                xs <> (x :: xs).
Proof.
 intros. induction xs as [| x' xs' IHxs'].
 - apply list_disj.
 - intros contra. injection  contra as Hc.
  apply IHxs'. rewrite <- Hc.  assumption.
Qed.

Lemma cons_inj : forall (X:Type) (x y : X) (xs ys : list X),
                  x :: xs = y :: ys -> x = y /\ xs = ys.
Proof.
  intros. injection H as Hc. split.
  - assumption.
  - assumption.
  Restart.
  intros. split. congruence. congruence.
Qed.

Theorem  list_disj1: forall (X :Type) (x  : X) (xs  : list X),
    ( nil <> (x :: xs)) .
Proof.
  apply
Qed.
