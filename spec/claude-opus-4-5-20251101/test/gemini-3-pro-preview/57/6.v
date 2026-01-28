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

Example test_monotonic : monotonic_spec [1; 2; 3; 2; 5; 60] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true -> ... *)
    intros H. discriminate H.
  - (* <- Direction: (is_increasing \/ is_decreasing) -> false = true *)
    intros [Hinc | Hdec].
    + (* Case Increasing: Contradiction at indices 2 and 3 (3 <= 2 is false) *)
      specialize (Hinc 2%nat 3%nat).
      simpl in Hinc.
      assert (H_range: (0 <= 2 < 3)%nat) by lia.
      assert (H_len: (3 < 6)%nat) by lia.
      specialize (Hinc H_range H_len).
      simpl in Hinc.
      lia.
    + (* Case Decreasing: Contradiction at indices 0 and 1 (1 >= 2 is false) *)
      specialize (Hdec 0%nat 1%nat).
      simpl in Hdec.
      assert (H_range: (0 <= 0 < 1)%nat) by lia.
      assert (H_len: (1 < 6)%nat) by lia.
      specialize (Hdec H_range H_len).
      simpl in Hdec.
      lia.
Qed.