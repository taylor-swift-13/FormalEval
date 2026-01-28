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

Example test_monotonic : monotonic_spec [-7; -9; 1; 3; -9; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true is impossible *)
    intros H. discriminate H.
  - (* <- Direction: Neither increasing nor decreasing implies false = true (contradiction) *)
    intros [H_inc | H_dec].
    + (* Case: Assume increasing, find counterexample at indices 0 and 1 (-7 > -9) *)
      unfold is_increasing in H_inc.
      specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (0 <= 0 < 1)%nat as H_range by lia.
      assert (1 < 6)%nat as H_len by lia.
      specialize (H_inc H_range H_len).
      simpl in H_inc.
      lia.
    + (* Case: Assume decreasing, find counterexample at indices 1 and 2 (-9 < 1) *)
      unfold is_decreasing in H_dec.
      specialize (H_dec 1%nat 2%nat).
      simpl in H_dec.
      assert (0 <= 1 < 2)%nat as H_range by lia.
      assert (2 < 6)%nat as H_len by lia.
      specialize (H_dec H_range H_len).
      simpl in H_dec.
      lia.
Qed.