Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_complex : monotonic_spec [1; 1; 3; 3; 2; 2; 4; 4; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + specialize (Hinc 3 4).
      assert (H : 3 < 4 < 9). { simpl. lia. }
      apply Hinc in H.
      simpl in H.
      lia.
    + specialize (Hdec 1 2).
      assert (H : 1 < 2 < 9). { simpl. lia. }
      apply Hdec in H.
      simpl in H.
      lia.
Qed.