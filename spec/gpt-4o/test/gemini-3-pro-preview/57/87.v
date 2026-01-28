Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_10_10_8_0_7_7 : monotonic_spec [10; 10; 8; 0; 7; 7] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + (* Contradiction for increasing *)
      specialize (H_inc 1 2).
      simpl in H_inc.
      assert (H : 1 < 2 < 6) by lia.
      apply H_inc in H.
      lia.
    + (* Contradiction for decreasing *)
      specialize (H_dec 3 4).
      simpl in H_dec.
      assert (H : 3 < 4 < 6) by lia.
      apply H_dec in H.
      lia.
Qed.