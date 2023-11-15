Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From LF Require Import Imp.

(*
Let's go back to the IMP language described in Imp.v

Consider the REPEAT construct, whose operational semantics is
described by the following rules


  st =[ c ]=>  st'       beval st' b = true
------------------------------------------------ (E_Re_End)
    st =[ REPEAT c UNTIL b END ] => st'


   st =[ c ]=>  st'   beval st' b = false  st' =[ REPEAT c UNTIL b END ] => st''
--------------------------------------------------------------------------------- (E_Re_Loop)
                st =[ REPEAT c UNTIL b END ] => st''


In fact, REPEAT does *not* need to be taken as primitive, but it can be
*defined* in terms of the constructors of com.

1.1. *Define* it in terms of the original language of com, using the
While construct. Fill in the following definition:
*)

Module RepeatDefined.

Definition REP (c : com) (b : bexp) : com :=
  CSeq c (CWhile (BNot b) c).

Definition REP' (c : com) (b : bexp) : com :=
  <{ c; while ~b do c end }>.

(*
1.2. Introduce an appropriate Notation.

1.3. Prove the above rules E_Re_End and E_Re_Loop are *derived*
rules. That is, they do not need to be defined inductively but just
stated and proven as Theorems, with respect to the original ceval
relation.

Again, do NOT redefine ceval.
*)

Notation "'repeat' c 'until' b 'end'" :=
         (REP c b)
            (in custom com at level 89, c at level 99, b at level 99) : com_scope.

Theorem E_Re_End : forall (c : com) (b : bexp) (st st' : state),
  st =[ c ]=> st' ->
  beval st' b = true ->
  st =[ repeat c until b end ]=> st'.
Proof.
  unfold REP. intros c b st st' H1 H2.
  apply E_Seq with (st' := st').
  - assumption.
  - apply E_WhileFalse. simpl. rewrite H2. reflexivity.
Qed.

Theorem E_Re_Loop' : forall (c : com) (b : bexp) (st st' st'' : state),
  st =[ c ]=> st' ->
  beval st' b = false ->
  st' =[ repeat c until b end ]=> st'' ->
  st  =[ repeat c until b end ]=> st''.
Proof.
  unfold REP. intros.
  inversion H1; subst. apply E_Seq with (st' := st').
  - assumption.
  - apply E_WhileTrue with (st' := st'0).
    + simpl. rewrite H0. reflexivity.
    + assumption.
    + assumption. 
Restart.
  unfold REP. intros.
  apply E_Seq with (st' := st').
  - assumption.
  - inversion H1; subst.
    + eapply E_WhileTrue; subst.
      * simpl. rewrite H0. reflexivity.
      * apply H4.
      * apply H7.
Qed.

(*
1.4 State and prove the inversion principle for the construct, that
is a Theorem like:

forall b c st st', st =[(REPEAT c UNTIL b END) => st' implies that
either b is true in st and st=[ c] => st' or there exists a st'' such
that ...

This theorem makes explicit the reasoning behind the inversion tactic
and corresponds to reading the two above rules from the bottom
up. It can be proven directly via inversion w/o any auxiliary
lemmas.
*)

Theorem inversion_principle: forall (c : com) (b : bexp) (st st' : state), 
  st =[ repeat c until b end ]=> st' ->
  beval st' b = true /\ st =[c]=> st' \/
  exists st'', beval st'' b = false /\
  st =[c]=> st'' /\ st'' =[repeat c until b end]=> st'.
Proof.
  unfold REP. intros.
  inversion H. subst.
  inversion H5; subst.
  - left. split.
    + simpl in H6. apply negb_false_iff in H6. assumption.
    + assumption.
  - right. subst. exists st'0. split.
    + simpl in H3. apply negb_true_iff in H3. assumption.
    + split.
      * assumption.
      * apply E_Seq with (st' := st'1).
        ** assumption.
        ** assumption.
Qed.

End RepeatDefined.
