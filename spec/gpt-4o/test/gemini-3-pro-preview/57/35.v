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

Example test_monotonic_complex : monotonic_spec [5; 1; -10; -7; -9; 1; 2; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (0 < 1 < 8)%nat as H by lia.
      apply Hinc in H.
      lia.
    + specialize (Hdec 2%nat 3%nat).
      simpl in Hdec.
      assert (2 < 3 < 8)%nat as H by lia.
      apply Hdec in H.
      lia.
Qed.