Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_mixed : monotonic_spec [2; 2; 1; 1; 1; 1; 4; 4; 6; 7] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [H_inc | H_dec].
    + (* Contradiction for increasing: 2 (at index 0) > 1 (at index 2) *)
      specialize (H_inc 0 2).
      simpl in H_inc.
      assert (H : 0 < 2 < 10) by lia.
      apply H_inc in H.
      simpl in H.
      lia.
    + (* Contradiction for decreasing: 1 (at index 5) < 4 (at index 6) *)
      specialize (H_dec 5 6).
      simpl in H_dec.
      assert (H : 5 < 6 < 10) by lia.
      apply H_dec in H.
      simpl in H.
      lia.
Qed.