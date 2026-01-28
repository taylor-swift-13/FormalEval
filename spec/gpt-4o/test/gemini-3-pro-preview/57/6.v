Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_2_3_2_5_60 : monotonic_spec [1; 2; 3; 2; 5; 60] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 2 3).
      simpl in Hinc.
      assert (H : 2 < 3 < 6) by lia.
      apply Hinc in H.
      lia.
    + specialize (Hdec 0 1).
      simpl in Hdec.
      assert (H : 0 < 1 < 6) by lia.
      apply Hdec in H.
      lia.
Qed.