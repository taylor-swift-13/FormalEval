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

Example test_monotonic : monotonic_spec [9; -7; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + unfold is_increasing in Hinc.
      specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (0 <= 0 < 1)%nat by lia.
      assert (1 < 3)%nat by lia.
      specialize (Hinc H H0).
      simpl in Hinc.
      lia.
    + unfold is_decreasing in Hdec.
      specialize (Hdec 1%nat 2%nat).
      simpl in Hdec.
      assert (0 <= 1 < 2)%nat by lia.
      assert (2 < 3)%nat by lia.
      specialize (Hdec H H0).
      simpl in Hdec.
      lia.
Qed.