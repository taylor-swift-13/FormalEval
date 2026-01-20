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

Example test_monotonic : monotonic_spec [5%Z; 4%Z; 3%Z; 3%Z; 3%Z; 2%Z; 4%Z] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + unfold is_increasing in Hinc.
      specialize (Hinc 5%nat 6%nat).
      simpl in Hinc.
      assert (H1: (0 <= 5 < 6)%nat) by lia.
      assert (H2: (6 < 7)%nat) by lia.
      specialize (Hinc H1 H2).
      lia.
    + unfold is_decreasing in Hdec.
      specialize (Hdec 5%nat 6%nat).
      simpl in Hdec.
      assert (H1: (0 <= 5 < 6)%nat) by lia.
      assert (H2: (6 < 7)%nat) by lia.
      specialize (Hdec H1 H2).
      lia.
Qed.