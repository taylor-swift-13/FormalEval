Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_3_2_7_4_2 : monotonic_spec [3; 2; 7; 4; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + (* Assume increasing, contradict with elements at indices 0 and 1 (3 > 2) *)
      specialize (Hinc 0 1).
      assert (H : 0 < 1 < 5) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + (* Assume decreasing, contradict with elements at indices 1 and 2 (2 < 7) *)
      specialize (Hdec 1 2).
      assert (H : 1 < 2 < 5) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.