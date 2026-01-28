Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_complex : monotonic_spec [2; 2; 1; 1; 2; 0; 1; 4; 4; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 1 2).
      simpl in Hinc.
      assert (Hbounds: 1 < 2 < 10) by lia.
      apply Hinc in Hbounds.
      simpl in Hbounds.
      lia.
    + specialize (Hdec 3 4).
      simpl in Hdec.
      assert (Hbounds: 3 < 4 < 10) by lia.
      apply Hdec in Hbounds.
      simpl in Hbounds.
      lia.
Qed.