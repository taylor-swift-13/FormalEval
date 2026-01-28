Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_2_1_2 : monotonic_spec [2; 1; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + assert (H : 0 < 1 < 3) by lia.
      specialize (H_inc 0 1 H).
      simpl in H_inc.
      lia.
    + assert (H : 1 < 2 < 3) by lia.
      specialize (H_dec 1 2 H).
      simpl in H_dec.
      lia.
Qed.