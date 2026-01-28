Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_1_3_3_2_2_4_4 : monotonic_spec [1; 1; 3; 3; 2; 2; 4; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H.
    discriminate.
  - intros [Hinc | Hdec].
    + (* Case Increasing: Counterexample at indices 3 and 4 (values 3 and 2) *)
      specialize (Hinc 3 4).
      simpl in Hinc.
      assert (H : 3 < 4 < 8) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + (* Case Decreasing: Counterexample at indices 1 and 2 (values 1 and 3) *)
      specialize (Hdec 1 2).
      simpl in Hdec.
      assert (H : 1 < 2 < 8) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.