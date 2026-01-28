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

Example test_monotonic_11_neg7_1_1 : monotonic_spec [11; -7; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert ((0 < 1 < 4)%nat) as H_bound by lia.
      apply H_inc in H_bound.
      lia.
    + specialize (H_dec 1%nat 2%nat).
      simpl in H_dec.
      assert ((1 < 2 < 4)%nat) as H_bound by lia.
      apply H_dec in H_bound.
      lia.
Qed.