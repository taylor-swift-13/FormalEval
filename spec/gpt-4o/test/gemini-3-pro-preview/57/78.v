Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_2_1_2_2_7_7 : monotonic_spec [2; 1; 2; 2; 7; 7] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0 1).
      simpl in H_inc.
      assert (0 < 1 < 6) as H_bounds by lia.
      apply H_inc in H_bounds.
      simpl in H_bounds.
      lia.
    + specialize (H_dec 1 2).
      simpl in H_dec.
      assert (1 < 2 < 6) as H_bounds by lia.
      apply H_dec in H_bounds.
      simpl in H_bounds.
      lia.
Qed.