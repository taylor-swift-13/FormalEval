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
  " "%char :: "t"%char :: "h"%char :: "i"%char :: "s"%char :: " "%char ::
  "i"%char :: "s"%char :: " "%char :: "b"%char :: "a"%char :: "a"%char ::
  "a"%char :: "c"%char :: "b"%char :: "a"%char :: "i"%char :: "c"%char ::
  "b"%char :: "b"%char :: "a"%char :: "t"%char :: nil.

Example test_is_happy_baaacbaicbbat : is_happy_spec test_string false.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hdistinct].
      specialize (Hdistinct 10).
      unfold three_consecutive_distinct in Hdistinct.
      simpl in Hdistinct.
      assert (H10: 10 + 2 < 22) by lia.
      apply Hdistinct in H10.
      destruct H10 as [H1 [H2 H3]].
      contradict H1.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 10.
      split.
      * simpl. lia.
      * simpl. left. reflexivity.
    + intro H.
      reflexivity.
Qed.