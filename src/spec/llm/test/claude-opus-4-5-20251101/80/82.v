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

Definition test_string : list ascii :=
  "b"%char :: "a"%char :: "a"%char :: "c"%char :: "b"%char :: "a"%char :: 
  "c"%char :: "b"%char :: "b"%char :: "R"%char :: "x"%char :: "b"%char :: 
  "t"%char :: "T"%char :: "U"%char :: "e"%char :: nil.

Example test_is_happy_baacbacbbRxbtTUe : is_happy_spec test_string false.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hdistinct].
      specialize (Hdistinct 1).
      unfold test_string in Hdistinct.
      simpl in Hdistinct.
      assert (H1: 1 + 2 < 16) by lia.
      specialize (Hdistinct H1).
      unfold three_consecutive_distinct in Hdistinct.
      simpl in Hdistinct.
      destruct Hdistinct as [Hneq1 [Hneq2 Hneq3]].
      contradiction Hneq1.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 1.
      split.
      * unfold test_string. simpl. lia.
      * unfold test_string. simpl. left. reflexivity.
    + intro H.
      reflexivity.
Qed.