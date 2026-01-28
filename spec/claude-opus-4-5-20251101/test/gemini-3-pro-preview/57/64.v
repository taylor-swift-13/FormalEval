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

Example test_monotonic : monotonic_spec [1; 1; 1; 2; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + unfold is_increasing in H_inc.
      specialize (H_inc 3%nat 4%nat).
      simpl in H_inc.
      assert (H_bounds: (0 <= 3 < 4)%nat /\ (4 < 6)%nat).
      { split; lia. }
      destruct H_bounds as [H_idx H_len].
      specialize (H_inc H_idx H_len).
      lia.
    + unfold is_decreasing in H_dec.
      specialize (H_dec 2%nat 3%nat).
      simpl in H_dec.
      assert (H_bounds: (0 <= 2 < 3)%nat /\ (3 < 6)%nat).
      { split; lia. }
      destruct H_bounds as [H_idx H_len].
      specialize (H_dec H_idx H_len).
      lia.
Qed.