Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_1_1_2_1_1_1_1 : monotonic_spec [1; 1; 1; 2; 1; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [H_inc | H_dec].
    + specialize (H_inc 3 4).
      assert (H_cond : 3 < 4 < 8).
      { simpl. lia. }
      apply H_inc in H_cond.
      simpl in H_cond.
      lia.
    + specialize (H_dec 2 3).
      assert (H_cond : 2 < 3 < 8).
      { simpl. lia. }
      apply H_dec in H_cond.
      simpl in H_cond.
      lia.
Qed.