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

Example test_monotonic_complex : monotonic_spec [5; 1; -10; 7; -9; 1; 2; 5; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (H_bounds : (0 < 1 < 9)%nat) by lia.
      apply H_inc in H_bounds.
      lia.
    + specialize (H_dec 2%nat 3%nat).
      simpl in H_dec.
      assert (H_bounds : (2 < 3 < 9)%nat) by lia.
      apply H_dec in H_bounds.
      lia.
Qed.