Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_1_3_5_4_5_6_5 : monotonic_spec [1; 1; 3; 5; 4; 5; 6; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + (* Not increasing: 5 (at index 3) > 4 (at index 4) *)
      specialize (Hinc 3 4).
      simpl in Hinc.
      assert (3 < 4 < 8) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + (* Not decreasing: 1 (at index 1) < 3 (at index 2) *)
      specialize (Hdec 1 2).
      simpl in Hdec.
      assert (1 < 2 < 8) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.