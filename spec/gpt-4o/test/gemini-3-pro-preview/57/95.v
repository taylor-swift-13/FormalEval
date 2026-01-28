Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_9_neg7_1_9 : monotonic_spec [9; -7; 1; 9] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + (* Case: Increasing *)
      specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (H : (0 < 1 < 4)%nat) by lia.
      apply Hinc in H.
      lia.
    + (* Case: Decreasing *)
      specialize (Hdec 1%nat 2%nat).
      simpl in Hdec.
      assert (H : (1 < 2 < 4)%nat) by lia.
      apply Hdec in H.
      lia.
Qed.