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

Example test_monotonic_complex : monotonic_spec [5; 1; -7; -9; 1; 5; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0%nat 1%nat).
      assert (H : (0 < 1 < 7)%nat) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 3%nat 4%nat).
      assert (H : (3 < 4 < 7)%nat) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.