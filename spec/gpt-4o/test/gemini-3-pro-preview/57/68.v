Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_mixed : monotonic_spec [4; 5; 3; 3; 3; 4; 3] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 1 2).
      simpl in Hinc.
      assert (H : 1 < 2 < 7) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 0 1).
      simpl in Hdec.
      assert (H : 0 < 1 < 7) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.