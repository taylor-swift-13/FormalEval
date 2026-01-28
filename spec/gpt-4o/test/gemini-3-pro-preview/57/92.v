Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_5_1_1_0_1_5 : monotonic_spec [5; 1; 1; 0; 1; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Contradiction for increasing: 5 (at 0) <= 1 (at 1) is false *)
      specialize (Hinc 0 1).
      simpl in Hinc.
      assert (0 < 1 < 6) as H by lia.
      apply Hinc in H.
      lia.
    + (* Contradiction for decreasing: 0 (at 3) >= 1 (at 4) is false *)
      specialize (Hdec 3 4).
      simpl in Hdec.
      assert (3 < 4 < 6) as H by lia.
      apply Hdec in H.
      lia.
Qed.