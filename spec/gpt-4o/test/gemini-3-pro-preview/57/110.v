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

Example test_monotonic_neg_2_to_neg_2 : monotonic_spec [-2; -1; 0; 1; 2; 1; 0; -1; -2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 4%nat 5%nat).
      simpl in Hinc.
      assert (H : (4 < 5 < 9)%nat). { split; lia. }
      apply Hinc in H.
      lia.
    + specialize (Hdec 0%nat 1%nat).
      simpl in Hdec.
      assert (H : (0 < 1 < 9)%nat). { split; lia. }
      apply Hdec in H.
      lia.
Qed.