Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_mixed : monotonic_spec [1; 1; 1; 2; 1; 3; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 3 4).
      simpl in Hinc.
      assert (H : 3 < 4 < 7) by lia.
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 2 3).
      simpl in Hdec.
      assert (H : 2 < 3 < 7) by lia.
      apply Hdec in H.
      simpl in H.
      lia.
Qed.