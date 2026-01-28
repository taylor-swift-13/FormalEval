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

Example test_monotonic_mixed : monotonic_spec [1; 1; -7; 1; 1; 2; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 1%nat 2%nat).
      simpl in Hinc.
      assert (H : (1 < 2 < 9)%nat) by lia.
      apply Hinc in H.
      lia.
    + specialize (Hdec 2%nat 3%nat).
      simpl in Hdec.
      assert (H : (2 < 3 < 9)%nat) by lia.
      apply Hdec in H.
      lia.
Qed.