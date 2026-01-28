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

Example test_monotonic : monotonic_spec [-11; 2; 7; 4; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + (* Refute is_increasing: 7 > 4 at indices 2 and 3 *)
      specialize (Hinc 2%nat 3%nat).
      simpl in Hinc.
      assert (H_range : (0 <= 2 < 3)%nat) by lia.
      assert (H_len : (3 < 5)%nat) by lia.
      specialize (Hinc H_range H_len).
      simpl in Hinc.
      lia.
    + (* Refute is_decreasing: -11 < 2 at indices 0 and 1 *)
      specialize (Hdec 0%nat 1%nat).
      simpl in Hdec.
      assert (H_range : (0 <= 0 < 1)%nat) by lia.
      assert (H_len : (1 < 5)%nat) by lia.
      specialize (Hdec H_range H_len).
      simpl in Hdec.
      lia.
Qed.