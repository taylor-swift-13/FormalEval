Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_1_1_2_1_1_1 : monotonic_spec [1; 1; 1; 2; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 3 4).
      simpl in H_inc.
      assert (3 < 4 < 7) as H_cond by lia.
      apply H_inc in H_cond.
      simpl in H_cond.
      lia.
    + specialize (H_dec 2 3).
      simpl in H_dec.
      assert (2 < 3 < 7) as H_cond by lia.
      apply H_dec in H_cond.
      simpl in H_cond.
      lia.
Qed.