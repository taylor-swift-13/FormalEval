Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_0_1_1_1 : monotonic_spec [1; 0; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0 1).
      simpl in Hinc.
      assert (Hcond : 0 < 1 < 5) by lia.
      apply Hinc in Hcond.
      simpl in Hcond.
      lia.
    + specialize (Hdec 1 2).
      simpl in Hdec.
      assert (Hcond : 1 < 2 < 5) by lia.
      apply Hdec in Hcond.
      simpl in Hcond.
      lia.
Qed.