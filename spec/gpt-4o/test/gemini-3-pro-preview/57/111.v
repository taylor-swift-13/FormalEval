Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_3_4_5_4_3_2_1 : monotonic_spec [1; 3; 4; 5; 4; 3; 2; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 3 4).
      simpl in Hinc.
      assert (3 < 4 < 8) as Hbounds by lia.
      apply Hinc in Hbounds.
      simpl in Hbounds.
      lia.
    + specialize (Hdec 0 1).
      simpl in Hdec.
      assert (0 < 1 < 8) as Hbounds by lia.
      apply Hdec in Hbounds.
      simpl in Hbounds.
      lia.
Qed.