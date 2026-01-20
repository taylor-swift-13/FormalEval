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

Definition zbjmzpzfak : list ascii :=
  ("z"%char :: "b"%char :: "j"%char :: "m"%char :: "z"%char :: "p"%char :: "z"%char :: "f"%char :: "a"%char :: "k"%char :: nil).

Example test_is_happy_zbjmzpzfak : is_happy_spec zbjmzpzfak false.
Proof.
  unfold is_happy_spec, zbjmzpzfak.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hdistinct].
      specialize (Hdistinct 4).
      assert (H4: 4 + 2 < 10) by lia.
      specialize (Hdistinct H4).
      unfold three_consecutive_distinct in Hdistinct.
      simpl in Hdistinct.
      destruct Hdistinct as [Hz1 [Hz2 Hz3]].
      contradict Hz2.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 4.
      split.
      * simpl. lia.
      * simpl.
        right. left.
        reflexivity.
    + intro H.
      reflexivity.
Qed.