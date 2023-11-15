From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.

Inductive month : Type :=
   | January
   | February : month
   | March : month
   | April : month
   | May : month
   | June : month
   | July : month
   | August : month
   | September : month
   | October : month
   | November : month
   | December : month  .


Definition month_len (leap:bool) (m:month) : nat :=
  match m with
  | February => if leap then 29 else 28
  | November | April | September | June => 30
  | _ => 31
  end.

Theorem days: forall   (m : month) (l : bool),
         28 <=? (month_len l m) = true.
Proof.
intros m l.
destruct m.
 - reflexivity.
 - destruct l.
   + reflexivity.
   + reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Restart.
intros []; try reflexivity.
intros [] ; reflexivity.
Qed.


(* using library facts*)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = 0 *)
    rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *)
    simpl. rewrite <- IHm'. rewrite  plus_n_Sm.
    reflexivity.  Qed.

Fixpoint nonzeros (l:list nat) : list nat :=
match l with
  | nil => nil
  | h :: t =>
      match h with
      | O => nonzeros t
      | S _ => h :: (nonzeros t)
      end
  end.

Lemma nonzeros_app : forall l1 l2 : list nat,
                       nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
 intros l1 l2.  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    destruct n as [| n'] eqn:E.
    + (* n = 0 *)
      simpl. rewrite IHl1'. reflexivity.
    + (* n = S n' *)
      simpl. rewrite IHl1'. reflexivity.  Qed.
