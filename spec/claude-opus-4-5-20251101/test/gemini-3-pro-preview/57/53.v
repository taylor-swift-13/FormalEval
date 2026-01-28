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

Example test_monotonic : monotonic_spec [3; 2; 6; 1; 7; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true implies anything *)
    intros H. discriminate.
  - (* <- Direction: (is_increasing \/ is_decreasing) -> false = true *)
    intros [Hinc | Hdec].
    + (* Case: is_increasing leads to contradiction *)
      unfold is_increasing in Hinc.
      (* Counter-example: indices 0 and 1 (values 3 and 2) violate increasing property *)
      specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (H_range: (0 <= 0 < 1)%nat) by lia.
      assert (H_len: (1 < 6)%nat) by lia.
      specialize (Hinc H_range H_len).
      simpl in Hinc.
      lia. (* 3 <= 2 is false *)
    + (* Case: is_decreasing leads to contradiction *)
      unfold is_decreasing in Hdec.
      (* Counter-example: indices 1 and 2 (values 2 and 6) violate decreasing property *)
      specialize (Hdec 1%nat 2%nat).
      simpl in Hdec.
      assert (H_range: (0 <= 1 < 2)%nat) by lia.
      assert (H_len: (2 < 6)%nat) by lia.
      specialize (Hdec H_range H_len).
      simpl in Hdec.
      lia. (* 2 >= 6 is false *)
Qed.