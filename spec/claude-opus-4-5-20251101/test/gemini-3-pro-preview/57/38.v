Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_increasing (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 <= nth j l 0.

Definition is_decreasing (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 >= nth j l 0.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> (is_increasing l \/ is_decreasing l).

Example test_monotonic : monotonic_spec [1; 1; 1; 2; 1; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + specialize (H_inc 3%nat 4%nat).
      assert (H_bounds: (0 <= 3 < 4)%nat /\ (4 < 8)%nat).
      { lia. }
      destruct H_bounds as [H_idx H_len].
      specialize (H_inc H_idx H_len).
      simpl in H_inc.
      lia.
    + specialize (H_dec 2%nat 3%nat).
      assert (H_bounds: (0 <= 2 < 3)%nat /\ (3 < 8)%nat).
      { lia. }
      destruct H_bounds as [H_idx H_len].
      specialize (H_dec H_idx H_len).
      simpl in H_dec.
      lia.
Qed.