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

Example test_monotonic_neg7_neg9_1_5 : monotonic_spec [-7; -9; 1; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (0 < 1 < 4)%nat by lia.
      apply H_inc in H.
      lia.
    + specialize (H_dec 1%nat 2%nat).
      simpl in H_dec.
      assert (1 < 2 < 4)%nat by lia.
      apply H_dec in H.
      lia.
Qed.