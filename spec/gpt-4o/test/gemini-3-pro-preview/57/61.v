Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_4_5_3_3_3_4 : monotonic_spec [4; 5; 3; 3; 3; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Case: Increasing *)
      (* Contradiction at indices 1 and 2: l[1]=5, l[2]=3, but 5 <= 3 is false *)
      specialize (Hinc 1 2).
      simpl in Hinc.
      assert (H : 1 < 2 < 6) by lia.
      apply Hinc in H.
      lia.
    + (* Case: Decreasing *)
      (* Contradiction at indices 0 and 1: l[0]=4, l[1]=5, but 4 >= 5 is false *)
      specialize (Hdec 0 1).
      simpl in Hdec.
      assert (H : 0 < 1 < 6) by lia.
      apply Hdec in H.
      lia.
Qed.