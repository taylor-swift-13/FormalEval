Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_5_4_3_3_3_2_4 : monotonic_spec [5; 4; 3; 3; 3; 2; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + specialize (H_inc 0 1).
      simpl in H_inc.
      assert (H_cond : 0 < 1 < 7) by lia.
      apply H_inc in H_cond.
      simpl in H_cond.
      lia.
    + specialize (H_dec 5 6).
      simpl in H_dec.
      assert (H_cond : 5 < 6 < 7) by lia.
      apply H_dec in H_cond.
      simpl in H_cond.
      lia.
Qed.