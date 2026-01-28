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

Example test_monotonic : monotonic_spec [1; 0; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [H | H].
    + unfold is_increasing in H.
      specialize (H 0%nat 1%nat).
      simpl in H.
      assert (0 <= 0 < 1)%nat by lia.
      assert (1 < 3)%nat by lia.
      apply H in H0; [| assumption].
      simpl in H0. lia.
    + unfold is_decreasing in H.
      specialize (H 1%nat 2%nat).
      simpl in H.
      assert (0 <= 1 < 2)%nat by lia.
      assert (2 < 3)%nat by lia.
      apply H in H0; [| assumption].
      simpl in H0. lia.
Qed.