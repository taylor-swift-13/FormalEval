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

Example test_monotonic_2_2_2_1_neg2_1 : monotonic_spec [2; 2; 2; 1; -2; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 2%nat 3%nat).
      assert (H_lt : (2 < 3 < 6)%nat) by lia.
      apply H_inc in H_lt.
      simpl in H_lt.
      lia.
    + specialize (H_dec 4%nat 5%nat).
      assert (H_lt : (4 < 5 < 6)%nat) by lia.
      apply H_dec in H_lt.
      simpl in H_lt.
      lia.
Qed.