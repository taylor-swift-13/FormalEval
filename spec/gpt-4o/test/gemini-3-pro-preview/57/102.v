Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_to_5_to_1 : monotonic_spec [1; 2; 3; 4; 5; 4; 3; 2; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + specialize (H 4 5).
      assert (C : 4 < 5 < 9). { simpl. lia. }
      apply H in C. simpl in C. lia.
    + specialize (H 3 4).
      assert (C : 3 < 4 < 9). { simpl. lia. }
      apply H in C. simpl in C. lia.
Qed.