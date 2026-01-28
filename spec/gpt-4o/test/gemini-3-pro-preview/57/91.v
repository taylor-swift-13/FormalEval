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

Example test_monotonic_neg : monotonic_spec [-11; -7; -9; -11; -11] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + specialize (H_inc 1%nat 2%nat).
      assert (H : (1 < 2 < 5)%nat) by lia.
      apply H_inc in H.
      simpl in H.
      lia.
    + specialize (H_dec 0%nat 1%nat).
      assert (H : (0 < 1 < 5)%nat) by lia.
      apply H_dec in H.
      simpl in H.
      lia.
Qed.