Require Import Coq.Lists.List.
Import ListNotations.

(* 3.1 Prove the following logical principles without automation:
no auto, no tauto, no firstorder *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HNQ HP. unfold not in HNQ.
  apply HNQ. apply H. apply HP.
Qed.

(*
3.1 bis: write the same proof as a text file in a mathematical form
using the rules of natural deduction: I'll get you started:

P, Q
P -> Q
 .
 .
 .

  (~Q -> ~P).
--------------------------------------- (-> intro)
 (P -> Q) -> (~Q -> ~P)
---------------------------------------------------------- (forall intro)
forall (P Q : Prop),  (P -> Q) -> (~Q -> ~P).
*)

Theorem dist_exists_or : forall (A : Type) (P Q : A -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x Hx]. destruct Hx as [HP | HQ].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x1 HP] | [x2 HQ]].
    + exists x1. left. apply HP.
    + exists x2. right. apply HQ.
Qed.

(* The double negation principle requires the following classical axiom *)
Axiom excluded_middle : forall P : Prop, P \/ ~P.

Theorem dnn: forall P, ~~P -> P.
Proof.
  intros P HNNP. destruct (excluded_middle P) as [HP | HNP].
  - apply HP.
  - unfold not in HNNP. unfold not in HNP.
    apply HNNP in HNP. destruct HNP.
Qed.

(* 3.2 State and prove the injectivity, disjointness and occur check
property for polymorphic List, similarly to what we did in class (Logic.v)
for Nats. To get you started, here is the statement for disjointness. *)

Theorem list_inj: forall (X : Type) (x y : X) (xs ys : list X),
  x :: xs = y :: ys -> x = y /\ xs = ys.
Proof.
  intros X x y xs ys H.
  injection H as H1 H2. split.
  - apply H1.
  - apply H2.
Qed.

Theorem list_disj: forall (X : Type) (x : X) (xs : list X),
  [] <> (x :: xs).
Proof.
  intros X x xs H. discriminate H.
Qed.

Theorem list_ock: forall (X : Type) (x : X) (xs : list X),
  xs <> (x :: xs).
Proof.
  induction xs as [| x' xs' IH].
  - intros H. discriminate H.
  - intros H. injection H as H1 H2.
    unfold not in IH. rewrite <- H1 in IH.
    apply IH. apply H2.
Qed.
