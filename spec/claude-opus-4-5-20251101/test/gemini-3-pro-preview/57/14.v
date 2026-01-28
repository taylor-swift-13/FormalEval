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

Example test_monotonic : monotonic_spec [1; 1; 1; 2; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [H | H].
    + unfold is_increasing in H.
      specialize (H 3%nat 4%nat).
      simpl in H.
      lia.
    + unfold is_decreasing in H.
      specialize (H 2%nat 3%nat).
      simpl in H.
      lia.
Qed.