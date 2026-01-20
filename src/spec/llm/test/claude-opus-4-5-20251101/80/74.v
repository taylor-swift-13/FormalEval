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
  " "%char :: "t"%char :: "h"%char :: "i"%char :: "s"%char :: " "%char :: " "%char :: " "%char :: "t"%char :: "h"%char :: "i"%char :: "s"%char :: "h"%char :: " "%char :: "i"%char :: " "%char :: "s"%char :: " "%char :: "b"%char :: " "%char :: "a"%char :: "b"%char :: "a"%char :: "t"%char :: "i"%char :: "s"%char :: " "%char :: "b"%char :: "a"%char :: "t"%char :: nil.

Example test_is_happy_thish : is_happy_spec test_string false.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hdistinct].
      specialize (Hdistinct 5).
      unfold test_string in Hdistinct.
      simpl in Hdistinct.
      assert (H5: 5 + 2 < 30) by lia.
      specialize (Hdistinct H5).
      unfold three_consecutive_distinct in Hdistinct.
      simpl in Hdistinct.
      destruct Hdistinct as [H1 [H2 H3]].
      exfalso.
      apply H3.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 5.
      split.
      * unfold test_string. simpl. lia.
      * unfold test_string. simpl. right. right. reflexivity.
    + intro H.
      reflexivity.
Qed.