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

Example test_monotonic : monotonic_spec [4; 5; 3; 3; 3; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true implies contradiction *)
    intros H.
    discriminate.
  - (* <- Direction: properties imply false = true (contradiction) *)
    intros [H_inc | H_dec].
    + (* Case: Increasing. Counter-example indices 1 (val 5) and 2 (val 3) *)
      specialize (H_inc 1%nat 2%nat).
      simpl in H_inc.
      assert (H_range : (0 <= 1 < 2)%nat) by lia.
      assert (H_len : (2 < 6)%nat) by lia.
      specialize (H_inc H_range H_len).
      lia.
    + (* Case: Decreasing. Counter-example indices 0 (val 4) and 1 (val 5) *)
      specialize (H_dec 0%nat 1%nat).
      simpl in H_dec.
      assert (H_range : (0 <= 0 < 1)%nat) by lia.
      assert (H_len : (1 < 6)%nat) by lia.
      specialize (H_dec H_range H_len).
      lia.
Qed.