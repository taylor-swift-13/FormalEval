Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_false : monotonic_spec [5; 2; 4; 3; 1; 2; 3; 4; 3; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0 1).
      simpl in Hinc.
      assert (0 < 1 < 10) as H by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 1 2).
      simpl in Hdec.
      assert (1 < 2 < 10) as H by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.