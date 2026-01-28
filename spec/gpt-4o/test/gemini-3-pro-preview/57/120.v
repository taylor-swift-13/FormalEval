Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_complex : monotonic_spec [2; 2; 1; 1; 2; 1; 1; 4; 4; 4; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0 2).
      assert (H_bounds : 0 < 2 < 11). { lia. }
      apply H_inc in H_bounds.
      simpl in H_bounds.
      lia.
    + specialize (H_dec 6 7).
      assert (H_bounds : 6 < 7 < 11). { lia. }
      apply H_dec in H_bounds.
      simpl in H_bounds.
      lia.
Qed.