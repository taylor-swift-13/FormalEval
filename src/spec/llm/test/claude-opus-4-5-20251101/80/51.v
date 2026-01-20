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

Example test_is_happy_yxycxyz : is_happy_spec ("y"%char :: "x"%char :: "y"%char :: "c"%char :: "x"%char :: "y"%char :: "z"%char :: nil) false.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hall].
      exfalso.
      assert (H02 : 0 + 2 < 7) by lia.
      specialize (Hall 0 H02).
      unfold three_consecutive_distinct in Hall.
      simpl in Hall.
      destruct Hall as [Hneq1 [Hneq2 _]].
      apply Hneq2.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 0.
      split.
      * simpl. lia.
      * simpl. right. left. reflexivity.
    + intro H.
      reflexivity.
Qed.