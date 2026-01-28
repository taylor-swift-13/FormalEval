Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_complex : monotonic_spec [10; 3; 5; 3; 2; 6; 9; 7; 5; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0 1).
      assert (0 < 1 < 10) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 1 2).
      assert (1 < 2 < 10) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.