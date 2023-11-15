(*
To be handed in by Oct 09, 2300 hour on upload.di.unimi.it

i. This file, filled

ii. For the paper proof(s), a txt file or a scan/jpg of handwritten
notes will suffice. Latex, markdown also welcomed, but not required

These exercises will *NOT* be evaluated strictly, but you'll get
"points" for partecipation, which  will be helful in rounding up
your final vote.

Do not use generative AI.
*)

From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.

Definition admit {T: Type} : T.  Admitted.

(*
1.1. Write an enumerated type for the month of the year

1.2 Write a function month_len that assigns to each month its length in days
keeping in mind that it could be a leap year, that is, month_len takes
a month and a boolean flag as arguments and returns a nat.

1.3 State and prove a theorem for which the result of month_len is
greater or equal to 28. You can use "leb", which is already defined in the library.
*)

Inductive month : Type :=
  | January
  |	February
  | March
  | April
  | May
  | June
  | July
  | August
  | September
  | October
  | November
  | December.

Definition month_len (m : month) (leap_year : bool) : nat :=
  match m with
  | February => if leap_year then 29 else 28
  | April | June | September | November => 30
  | _ => 31
  end.

(* https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html#try *)

Theorem month_len_gte_28 : forall (m : month) (leap_year : bool),
  28 <=? (month_len m leap_year) = true.
Proof. (* Naive version *)
  intros m leap_year.
  destruct m.
  - reflexivity.
  - destruct leap_year.
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
Restart. (* Better version *)
  intros m leap_year.
  destruct m; try reflexivity.
  (* Only February is left *)
  destruct leap_year.
  - reflexivity.
  - reflexivity.
Qed.

(*
2.1. Prove the following theorem. You're going to need some
lemma(s). You can either prove them directly (they are very easy), or
try to find them in the Coq library. In the latter case, the "Search
<id>" command is very useful.

Example: Search Nat.add.
*)

Lemma plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m,
  n + (S m) = S (n + m).
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite -> plus_0_r. reflexivity.
  - simpl.
    rewrite -> plus_n_Sm.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* 2.2 Write on paper the above proof, skipping the proofs of the
intermendiate lemmas, but detailing their use, as well as the use of
simplication, IH etc. Do *not* just verbalize the proof script, try to
write a math proof as in the notes. *)

(* 3.1 Complete the definition of nonzeros, a function that removes
O's from a list of nats *)

Fixpoint nonzeros (l: list nat) : list nat :=
  match l with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

(* 3.2 State and prove a lemma that says that nonzeros distributes
over the concatenaton (append) of two lists. Remember that a nested match in
the function definition corresponds to a destruct in the proof script. *)

Lemma nonzeros_app : forall l1 l2 : list nat,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. destruct n as [| n'] eqn:En.
    + rewrite -> IHl1'. reflexivity.
    + rewrite -> IHl1'. reflexivity.
Qed.
