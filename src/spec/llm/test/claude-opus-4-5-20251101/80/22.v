Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition three_consecutive_distinct (s : list ascii) (i : nat) : Prop :=
  match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
  | Some c1, Some c2, Some c3 => c1 <> c2 /\ c1 <> c3 /\ c2 <> c3
  | _, _, _ => False
  end.

Definition is_happy_spec (s : list ascii) (result : bool) : Prop :=
  (result = true <->
    (length s >= 3 /\
     forall i, i + 2 < length s -> three_consecutive_distinct s i)) /\
  (result = false <->
    (length s < 3 \/
     exists i, i + 2 < length s /\
       match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
       | Some c1, Some c2, Some c3 => c1 = c2 \/ c1 = c3 \/ c2 = c3
       | _, _, _ => False
       end)).

Definition bjmzpzkfak : list ascii :=
  ("b"%char :: "j"%char :: "m"%char :: "z"%char :: "p"%char :: "z"%char :: "k"%char :: "f"%char :: "a"%char :: "k"%char :: nil).

Example test_is_happy_bjmzpzkfak : is_happy_spec bjmzpzkfak false.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hall].
      assert (H3 : 3 + 2 < 10) by lia.
      specialize (Hall 3 H3).
      unfold three_consecutive_distinct in Hall.
      unfold bjmzpzkfak in Hall.
      simpl in Hall.
      destruct Hall as [Hneq1 [Hneq2 Hneq3]].
      exfalso.
      apply Hneq2.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 3.
      split.
      * unfold bjmzpzkfak. simpl. lia.
      * unfold bjmzpzkfak. simpl.
        right. left. reflexivity.
    + intro H.
      reflexivity.
Qed.