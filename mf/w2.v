(* To be handed in by Oct 16, 2300 hour on upload.di.unimi.it *)
Require Import Coq.Lists.List.
Import ListNotations.

Definition admit {T: Type} : T. Admitted.

(* 1. Consider the  classical definition of the function [fold] (right) *)

(*
Intuitively, the behavior of the [fold] operation is to
insert a given binary operator [f] between every pair of elements
in a given list. For example, [ fold plus [1;2;3;4] ] intuitively
means [1+2+3+4]. To make this precise, we also need a "starting
element" that serves as the initial second input to [f].

So, for example,
    fold (fun x y => x + y) [1;2;3;4] 0
yields
    1 + (2 + (3 + (4 + 0))).
*)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(*
1.1 As well known, many common functions on lists can be
implemented in terms of fold.

Define [fold_length] that redefines the length of a poly list
via [fold].
*)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length_1 : @fold_length nat [] = 0.
Proof. reflexivity. Qed.

Example test_fold_length_2 : fold_length [0;1;2;3;4] = 5.
Proof. reflexivity. Qed.

Example test_fold_length_3 : fold_length [1;2;3] = S (S (S 0)).
Proof. reflexivity. Qed.

(* 1.2 Show that [fold_length] is equivalent to [length] *)

Theorem fold_length_correct : forall (X : Type) (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
Qed.

(* 2. Rember the definitions of [map] and (naive[rev]) *)
Print rev.
Print map.

(* 2.1 Show that map and rev commute. You need to prove an auxiliary lemma.
Try to state it as general as possible. *)

Lemma map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. rewrite -> map_app. reflexivity.
Qed.
