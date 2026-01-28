Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_10_9_8_7_11_6 : monotonic_spec [10; 9; 8; 7; 11; 6] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0 1).
      simpl in Hinc.
      assert (0 < 1 < 6) by lia.
      apply Hinc in H.
      lia.
    + specialize (Hdec 3 4).
      simpl in Hdec.
      assert (3 < 4 < 6) by lia.
      apply Hdec in H.
      lia.
Qed.