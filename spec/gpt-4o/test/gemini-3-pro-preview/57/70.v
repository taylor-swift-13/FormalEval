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

Example test_monotonic_9_neg7_1 : monotonic_spec [9; -7; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (0 < 1 < 3)%nat as H by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 1%nat 2%nat).
      simpl in Hdec.
      assert (1 < 2 < 3)%nat as H by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.