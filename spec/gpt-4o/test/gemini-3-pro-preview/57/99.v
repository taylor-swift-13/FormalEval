Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_10_9_8_7_8_7_7_7 : monotonic_spec [10; 9; 8; 7; 8; 7; 7; 7] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H.
    discriminate.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0 1).
      simpl in H_inc.
      assert (0 < 1 < 8) as H by lia.
      apply H_inc in H.
      simpl in H.
      lia.
    + specialize (H_dec 3 4).
      simpl in H_dec.
      assert (3 < 4 < 8) as H by lia.
      apply H_dec in H.
      simpl in H.
      lia.
Qed.