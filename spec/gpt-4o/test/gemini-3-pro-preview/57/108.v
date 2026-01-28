Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_5_4_3_2_1_1_1_2_3_4_5 : monotonic_spec [5; 4; 3; 2; 1; 1; 1; 2; 3; 4; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0 1).
      simpl in H_inc.
      assert (H_bound : 0 < 1 < 11) by lia.
      apply H_inc in H_bound.
      simpl in H_bound.
      lia.
    + specialize (H_dec 6 7).
      simpl in H_dec.
      assert (H_bound : 6 < 7 < 11) by lia.
      apply H_dec in H_bound.
      simpl in H_bound.
      lia.
Qed.