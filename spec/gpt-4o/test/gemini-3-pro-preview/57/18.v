Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j /\ j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j /\ j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_3_2_4 : monotonic_spec [1; 3; 2; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 1 2).
      simpl in Hinc.
      assert (H : 1 < 2 /\ 2 < 4) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 0 1).
      simpl in Hdec.
      assert (H : 0 < 1 /\ 1 < 4) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.