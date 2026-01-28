Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_2_5_4_3_3_3_2_1_1 : monotonic_spec [2; 5; 4; 3; 3; 3; 2; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + assert (H : 1 < 2 < 9) by lia.
      specialize (Hinc 1 2 H).
      simpl in Hinc.
      lia.
    + assert (H : 0 < 1 < 9) by lia.
      specialize (Hdec 0 1 H).
      simpl in Hdec.
      lia.
Qed.