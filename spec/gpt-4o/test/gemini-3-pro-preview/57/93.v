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

Example test_monotonic_neg_11_0_10_1_1_10 : monotonic_spec [-11; 0; 10; 1; 1; 10] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + assert (H : (2 < 3 < 6)%nat) by lia.
      specialize (Hinc 2%nat 3%nat H).
      simpl in Hinc.
      lia.
    + assert (H : (0 < 1 < 6)%nat) by lia.
      specialize (Hdec 0%nat 1%nat H).
      simpl in Hdec.
      lia.
Qed.