Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_5_4_3_3_7_2_1 : monotonic_spec [5; 4; 3; 3; 7; 2; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0 1).
      simpl in Hinc.
      assert (0 < 1 < 7) by lia.
      apply Hinc in H.
      lia.
    + specialize (Hdec 3 4).
      simpl in Hdec.
      assert (3 < 4 < 7) by lia.
      apply Hdec in H.
      lia.
Qed.