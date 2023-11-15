Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.

(* 1. Going back to the given inductive definitions, prove the other
side of the inclusion. You will need a lemma first. *)

Inductive beautiful : nat -> Prop :=
| b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Inductive gorgeous : nat -> Prop :=
| g_0     : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [| n' Hn' IH | n' Hn' IH].
  - simpl. assumption.
  - apply g_plus3 in IH. assumption.
  - apply g_plus5 in IH. assumption.
Qed.

Theorem beautiful_gorgeous : forall n,
  beautiful n -> gorgeous n.
Proof.
  intros n H. induction H as [| | | n' m' Hn' IHn' Hm' IHm'].
  - apply g_0.
  - apply g_plus3. apply g_0.
  - apply g_plus5. apply g_0.
  - apply gorgeous_sum.
    + assumption.
    + assumption.
Qed.

(** Write a txt file with the mathematical proof: I'll get you started with
the more involved case:

Theorem beautiful_gorgeous : forall n, beautiful n -> gorgeous n.

Proof: by induction on the derivation H : beautiful n:

Case H =   H1: beautiful n  H2: beautiful m
                -------------------------------------------
                              beautiful n + m

gorgeous n                    By IH applied to H1
gorgeous m                   By IH applied to H2
gorgeous n + m            By lemma ...
                                     QED

Complete the other cases specifying which rules you are applying as above
*)

(** 2. In this exercise we study some properties of the less-or-equal relation.
Some of them are not completely trivial and require previous lemmas, so think
before you start writing tactics *)

Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
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
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H as [H1 | m' H1 H2].
  - apply le_n.
  - rewrite <- H1. apply le_S. apply le_n.
Qed.

(** Most of the results above are needed in the following, where I'll start
the proof, since it requires the IH to be general enough. Remember that < is
defined in terms of <= *)

Print Peano.lt.

Theorem lt_ge_cases : forall  m n,
  n < m \/ n >= m.
Proof.
  intros m. induction m as [| m' IHm].
  - right. apply O_le_n.
  - induction n as [| n' IHn].
    + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
    + destruct IHn as [IHn' | IHn'].
      * destruct IHn' as [| n'' IHn''].
        ** right. apply le_n.
        ** left. apply n_le_m__Sn_le_Sm. assumption.
      * right. apply le_S. assumption.
Qed.

Theorem lt_ge_cases' : forall  m n,
  n < m \/ n >= m.
Proof.
  intros m. induction m as [| m' IH].
  - intros n. right. apply O_le_n.
  - intros n. destruct n as [| n'] eqn:E.
    + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
    + destruct IH with (n := n').
      * left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply n_le_m__Sn_le_Sm. apply H.
Qed.

(** Prove the following equivalence between boolean and propositional
less-or-equal. You will need some of the above lemmas *)

Lemma leb_true : forall n m,
  (n <=? m) = true -> n <= m.
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

Lemma le_leb : forall n m,
  n <= m -> (n <=? m) = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IH].
  - intros n H. inversion H. reflexivity.
  - intros n H. destruct n as [| n'] eqn:E.
    + simpl. reflexivity.
    + simpl. apply Sn_le_Sm__n_le_m in H. apply IH. assumption.
Qed.

Theorem leb_le : forall n m,
  (n <=? m) = true <-> n <= m.
Proof.
  intro n. induction n as [| n' IH].
  - split.
    + intros H. apply O_le_n.
    + intros H. simpl. reflexivity.
  - split.
    + intros H. apply leb_true in H. assumption.
    + intros H. apply le_leb. assumption.
Qed.

Theorem leb_le' : forall n m,
  (n <=? m) = true <-> n <= m.
Proof.
  intros n. induction n as [| n' IHn].
  - intros m. split.
    + intros H. apply O_le_n.
    + intros H. simpl. reflexivity.
  - intros m. split.
    + intros H. destruct m as [| m'] eqn:E.
      * inversion H.
      * apply n_le_m__Sn_le_Sm. apply IHn. apply H.
    + intros H. destruct m as [| m'] eqn:E.
      * inversion H.
      * apply IHn. apply Sn_le_Sm__n_le_m. apply H.
Qed.
