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

Example test_monotonic : monotonic_spec [2; 1; 2; 2; 7; 7] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true implies anything *)
    intros H. discriminate.
  - (* <- Direction: contradiction from assumption that list is monotonic *)
    intros [H_inc | H_dec].
    + (* Assume increasing, find counter-example at indices 0 and 1 *)
      specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (H_bounds : (0 <= 0 < 1)%nat /\ (1 < 6)%nat) by lia.
      destruct H_bounds as [H_range H_len].
      specialize (H_inc H_range H_len).
      lia. (* 2 <= 1 is False *)
    + (* Assume decreasing, find counter-example at indices 1 and 2 *)
      specialize (H_dec 1%nat 2%nat).
      simpl in H_dec.
      assert (H_bounds : (0 <= 1 < 2)%nat /\ (2 < 6)%nat) by lia.
      destruct H_bounds as [H_range H_len].
      specialize (H_dec H_range H_len).
      lia. (* 1 >= 2 is False *)
Qed.