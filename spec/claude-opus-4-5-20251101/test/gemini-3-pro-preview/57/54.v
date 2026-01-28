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

Example test_monotonic : monotonic_spec [1; 1; 1; 1; 2; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true implies contradiction *)
    intros H. discriminate.
  - (* <- Direction: Prove negation of increasing or decreasing *)
    intros [Hinc | Hdec].
    + (* Case: Assume increasing, find counter-example at indices 4 and 5 (2 > 1) *)
      unfold is_increasing in Hinc.
      specialize (Hinc 4%nat 5%nat).
      simpl in Hinc.
      assert (H_range: (0 <= 4 < 5)%nat) by lia.
      assert (H_len: (5 < 7)%nat) by lia.
      specialize (Hinc H_range H_len).
      lia.
    + (* Case: Assume decreasing, find counter-example at indices 3 and 4 (1 < 2) *)
      unfold is_decreasing in Hdec.
      specialize (Hdec 3%nat 4%nat).
      simpl in Hdec.
      assert (H_range: (0 <= 3 < 4)%nat) by lia.
      assert (H_len: (4 < 7)%nat) by lia.
      specialize (Hdec H_range H_len).
      lia.
Qed.