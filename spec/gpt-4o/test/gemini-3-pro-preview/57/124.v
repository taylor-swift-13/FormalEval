Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_1_3_5_4_4_6 : monotonic_spec [1; 1; 3; 5; 4; 4; 6] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 3 4).
      simpl in Hinc.
      assert (3 < 4 < 7) as Hbounds by lia.
      apply Hinc in Hbounds.
      lia.
    + specialize (Hdec 1 2).
      simpl in Hdec.
      assert (1 < 2 < 7) as Hbounds by lia.
      apply Hdec in Hbounds.
      lia.
Qed.