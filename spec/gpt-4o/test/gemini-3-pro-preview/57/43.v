Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j : nat, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j : nat, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_5_1_neg10_neg9_1_2_5 : monotonic_spec [5; 1; -10; -9; 1; 2; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (H : (0 < 1 < 7)%nat) by lia.
      specialize (Hinc H).
      lia.
    + specialize (Hdec 2%nat 3%nat).
      simpl in Hdec.
      assert (H : (2 < 3 < 7)%nat) by lia.
      specialize (Hdec H).
      lia.
Qed.