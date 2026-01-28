Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_2_2_1_1_1_1_4_4_6_1 : monotonic_spec [2; 2; 1; 1; 1; 1; 4; 4; 6; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 1 2).
      simpl in Hinc.
      assert (H : 1 < 2 < 10) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 5 6).
      simpl in Hdec.
      assert (H : 5 < 6 < 10) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.