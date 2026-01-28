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

Example test_happy_case : is_happy_spec ["b"; "a"; "a"; "c"; "b"; "a"; "c"; "b"] false.
Proof.
  unfold is_happy_spec.
  split.
  - split; intro H.
    + discriminate H.
    + destruct H as [_ Hforall].
      specialize (Hforall 0).
      assert (Hlen : 0 + 2 < 8). { simpl. lia. }
      apply Hforall in Hlen.
      unfold three_consecutive_distinct in Hlen.
      simpl in Hlen.
      destruct Hlen as [_ [_ Hcontra]].
      congruence.
  - split; intro H.
    + right.
      exists 0.
      split.
      * simpl. lia.
      * simpl. right. right. reflexivity.
    + reflexivity.
Qed.