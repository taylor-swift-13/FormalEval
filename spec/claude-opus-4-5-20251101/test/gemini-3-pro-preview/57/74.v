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

Example test_monotonic : monotonic_spec [3; 1; 3; 2; 3] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true is impossible *)
    intros H. discriminate.
  - (* <- Direction: Neither increasing nor decreasing implies false = true (vacuously true if premises are false) *)
    (* Actually, we need to show that (is_increasing \/ is_decreasing) leads to a contradiction *)
    intros [Hinc | Hdec].
    + (* Refute is_increasing *)
      unfold is_increasing in Hinc.
      (* Counterexample at indices 0 and 1: 3 <= 1 is false *)
      specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (H_bounds : (0 <= 0 < 1)%nat /\ (1 < 5)%nat) by lia.
      destruct H_bounds as [H1 H2].
      specialize (Hinc H1 H2).
      lia.
    + (* Refute is_decreasing *)
      unfold is_decreasing in Hdec.
      (* Counterexample at indices 1 and 2: 1 >= 3 is false *)
      specialize (Hdec 1%nat 2%nat).
      simpl in Hdec.
      assert (H_bounds : (0 <= 1 < 2)%nat /\ (2 < 5)%nat) by lia.
      destruct H_bounds as [H1 H2].
      specialize (Hdec H1 H2).
      lia.
Qed.