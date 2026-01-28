Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_9_neg7_1_9_9_neg7 : monotonic_spec [9; -7; 1; 9; 9; -7] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0%nat 1%nat).
      assert (H_bounds : (0 < 1 < 6)%nat) by lia.
      apply H_inc in H_bounds.
      simpl in H_bounds.
      lia.
    + specialize (H_dec 1%nat 2%nat).
      assert (H_bounds : (1 < 2 < 6)%nat) by lia.
      apply H_dec in H_bounds.
      simpl in H_bounds.
      lia.
Qed.