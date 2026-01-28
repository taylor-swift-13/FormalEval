Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_20_4_10 : monotonic_spec [1; 20; 4; 10] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_asc | H_desc].
    + specialize (H_asc 1 2).
      simpl in H_asc.
      assert (H_bound : 1 < 2 < 4) by lia.
      apply H_asc in H_bound.
      simpl in H_bound.
      lia.
    + specialize (H_desc 0 1).
      simpl in H_desc.
      assert (H_bound : 0 < 1 < 4) by lia.
      apply H_desc in H_bound.
      simpl in H_bound.
      lia.
Qed.