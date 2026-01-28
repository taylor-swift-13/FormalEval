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

Example test_monotonic_neg11_2_7_4_2 : monotonic_spec [-11; 2; 7; 4; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 2%nat 3%nat).
      simpl in Hinc.
      assert (H : (2 < 3 < 5)%nat) by lia.
      apply Hinc in H.
      lia.
    + specialize (Hdec 0%nat 1%nat).
      simpl in Hdec.
      assert (H : (0 < 1 < 5)%nat) by lia.
      apply Hdec in H.
      lia.
Qed.