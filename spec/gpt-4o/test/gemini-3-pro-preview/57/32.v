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

Example test_monotonic_5_1_neg9_1_5 : monotonic_spec [5; 1; -9; 1; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + assert (H : (0 < 1 < 5)%nat) by lia.
      specialize (Hinc 0%nat 1%nat H).
      simpl in Hinc.
      lia.
    + assert (H : (2 < 3 < 5)%nat) by lia.
      specialize (Hdec 2%nat 3%nat H).
      simpl in Hdec.
      lia.
Qed.