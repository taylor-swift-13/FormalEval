Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_1_5_1_1_1 : monotonic_spec [1; 1; 5; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + (* Case: Increasing *)
      specialize (H_inc 2 3).
      simpl in H_inc.
      assert (H_cond : 2 < 3 < 6) by lia.
      apply H_inc in H_cond.
      simpl in H_cond.
      lia.
    + (* Case: Decreasing *)
      specialize (H_dec 1 2).
      simpl in H_dec.
      assert (H_cond : 1 < 2 < 6) by lia.
      apply H_dec in H_cond.
      simpl in H_cond.
      lia.
Qed.