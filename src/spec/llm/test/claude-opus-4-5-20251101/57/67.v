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

Example test_monotonic : monotonic_spec [-7%Z; -9%Z; 1%Z; -9%Z; 5%Z] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + unfold is_increasing in Hinc.
      assert (H01: (0 <= 0 < 1)%nat) by lia.
      assert (H1len: (1 < 5)%nat) by (simpl; lia).
      specialize (Hinc 0%nat 1%nat H01 H1len).
      simpl in Hinc.
      lia.
    + unfold is_decreasing in Hdec.
      assert (H12: (0 <= 1 < 2)%nat) by lia.
      assert (H2len: (2 < 5)%nat) by (simpl; lia).
      specialize (Hdec 1%nat 2%nat H12 H2len).
      simpl in Hdec.
      lia.
Qed.