Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_complex : monotonic_spec [5; 4; 3; 10; 2; 1; 1; 1; 2; 3; 4; 5; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0 1).
      simpl in Hinc.
      assert (Hbound: 0 < 1 < 13) by lia.
      apply Hinc in Hbound.
      simpl in Hbound.
      lia.
    + specialize (Hdec 2 3).
      simpl in Hdec.
      assert (Hbound: 2 < 3 < 13) by lia.
      apply Hdec in Hbound.
      simpl in Hbound.
      lia.
Qed.