Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope char_scope.

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

Example test_happy_case : is_happy_spec ["y"; "y"; "y"; "y"; "y"] false.
Proof.
  unfold is_happy_spec.
  split.
  - split; intro H.
    + discriminate H.
    + destruct H as [_ H].
      specialize (H 0).
      simpl in H.
      assert (Hlen: 0 + 2 < 5) by lia.
      apply H in Hlen.
      destruct Hlen as [Hneq _].
      contradiction Hneq; reflexivity.
  - split; intro H.
    + right.
      exists 0.
      split.
      * simpl; lia.
      * simpl. left. reflexivity.
    + reflexivity.
Qed.