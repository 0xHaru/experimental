From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(* Remember the definition of arithmetic and Boolean expression
and their interpreters: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* This is the optimizer for arith expressions *)

Fixpoint opt_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      opt_0plus e2  (* <-- here ! *)
  | APlus e1 e2 =>
      APlus (opt_0plus e1) (opt_0plus e2)
  | AMinus e1 e2 =>
      AMinus (opt_0plus e1) (opt_0plus e2)
  | AMult e1 e2 =>
      AMult (opt_0plus e1) (opt_0plus e2)
  end.

Theorem opt_0plus_sound: forall a,
  aeval (opt_0plus a) = aeval a.
Proof.
  intros a. induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity.
Qed.

(*
1. Define a similar optimization on Boolean expression:

Fixpoint opt_b (b : bexp) : bexp :=
...

such that

  - on arithmetic sub-expressions, it applies the above optimization
    opt_0plus
  - further, it performs the following optimization:
    - (true and b) is optimized to to b
    - (false and b) is optimized  to false
*)

Fixpoint opt_b (b : bexp) : bexp :=
  match b with
  | BTrue          => BTrue
  | BFalse         => BFalse
  | BEq a1 a2      => BEq (opt_0plus a1) (opt_0plus a2)
  | BLe a1 a2      => BLe (opt_0plus a1) (opt_0plus a2)
  | BNot b1        => BNot (opt_b b1)
  | BAnd BTrue b2  => opt_b b2
  | BAnd BFalse b2 => BFalse
  | BAnd b1 b2     => BAnd (opt_b b1) (opt_b b2)
  end.

(* 2. Prove that the transformation over Booleans is sound. Use the
tacticals we've seen so far to make the proof as short and modular
as possible. *)

Lemma negb_impl : forall (b1 b2 : bool),
  b1 = b2 <-> negb b1 = negb b2.
Proof.
  intros b1 b2. split.
  - intros H. rewrite H. reflexivity.
  - intros H. destruct b1, b2 eqn:E.
    + reflexivity.
    + discriminate H.
    + discriminate H.
    + reflexivity.
Restart.
  intros b1 b2. split.
  - intros H. rewrite H. reflexivity.
  - intros H. destruct b1, b2 eqn:E;
      try (reflexivity);
      try (discriminate H).
Qed.

Theorem opt_b_sound: forall b,
  beval (opt_b b) = beval b.
Proof.
  intros b. induction b.
  - (* BTrue *) simpl. reflexivity.
  - (* BFalse *) simpl. reflexivity.
  - (* BEq *) simpl.
    rewrite opt_0plus_sound. rewrite opt_0plus_sound.
    reflexivity.
  - (* BLe *) simpl.
    rewrite opt_0plus_sound. rewrite opt_0plus_sound.
    reflexivity.
  - (* BNot *) simpl. destruct b eqn:E.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl.
      rewrite opt_0plus_sound. rewrite opt_0plus_sound.
      reflexivity.
    + simpl.
      rewrite opt_0plus_sound. rewrite opt_0plus_sound.
      reflexivity.
    + (* Search (negb (negb ?X) = ?X). *) simpl in *.
      rewrite negb_involutive. rewrite negb_involutive.
      apply negb_impl in IHb. assumption.
    + apply negb_impl in IHb. assumption.
  - (* BAnd *) simpl. destruct b1 eqn:E.
    + simpl. assumption.
    + simpl. reflexivity.
    + simpl.
      rewrite opt_0plus_sound. rewrite opt_0plus_sound.
      rewrite IHb2. reflexivity.
    + simpl.
      rewrite opt_0plus_sound. rewrite opt_0plus_sound.
      rewrite IHb2. reflexivity.
    + simpl in *. rewrite IHb2. rewrite IHb1. reflexivity.
    + rewrite <- IHb1. rewrite <- IHb2. reflexivity.
Qed.

Theorem opt_b_sound': forall b,
  beval (opt_b b) = beval b.
Proof.
  intros b. induction b;
    (* BTrue, BFalse *)
    try (simpl; reflexivity);
    (* BEq, BLe *)
    try (simpl; repeat (rewrite opt_0plus_sound); reflexivity).
  - (* BNot *) simpl. destruct b eqn:E;
      try (simpl; reflexivity);
      try (simpl; repeat (rewrite opt_0plus_sound); reflexivity).
    + (* Search (negb (negb ?X) = ?X). *) simpl in *.
      repeat (rewrite negb_involutive).
      apply negb_impl in IHb. assumption.
    + apply negb_impl in IHb. assumption.
  - (* BAnd *) simpl. destruct b1 eqn:E;
      try (simpl; repeat (rewrite opt_0plus_sound);
           rewrite IHb2; reflexivity).
    + simpl. assumption.
    + simpl in *. rewrite IHb2. rewrite IHb1. reflexivity.
    + rewrite <- IHb1. rewrite <- IHb2. reflexivity.
Qed.
