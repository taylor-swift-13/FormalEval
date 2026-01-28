Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_complex : monotonic_spec [10; 2; 5; 3; 2; 6; 9; 7; 5; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0 1).
      simpl in H_inc.
      assert (H : 0 < 1 < 10) by lia.
      apply H_inc in H.
      simpl in H.
      lia.
    + specialize (H_dec 1 2).
      simpl in H_dec.
      assert (H : 1 < 2 < 10) by lia.
      apply H_dec in H.
      simpl in H.
      lia.
Qed.