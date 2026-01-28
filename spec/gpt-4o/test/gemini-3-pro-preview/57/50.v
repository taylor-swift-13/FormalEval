Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_3_6_2_6_7_2 : monotonic_spec [3; 6; 2; 6; 7; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 1 2).
      assert (H : 1 < 2 < 6) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 0 1).
      assert (H : 0 < 1 < 6) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.