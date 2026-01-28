Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_2_2_2_neg2_1 : monotonic_spec [2; 2; 2; -2; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 2%nat 3%nat).
      simpl in Hinc.
      assert (Hbound: (2 < 3 < 5)%nat). { lia. }
      apply Hinc in Hbound.
      lia.
    + specialize (Hdec 3%nat 4%nat).
      simpl in Hdec.
      assert (Hbound: (3 < 4 < 5)%nat). { lia. }
      apply Hdec in Hbound.
      lia.
Qed.