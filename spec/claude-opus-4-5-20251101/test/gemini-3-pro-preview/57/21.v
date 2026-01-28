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

Example test_monotonic : monotonic_spec [5; 1; 1; -7; 1; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + (* Case: is_increasing. Counterexample: indices 0 and 1 (5 <= 1 is false) *)
      specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (H_bounds : (0 <= 0 < 1)%nat /\ (1 < 6)%nat) by lia.
      destruct H_bounds as [H_range H_len].
      specialize (H_inc H_range H_len).
      lia.
    + (* Case: is_decreasing. Counterexample: indices 3 and 4 (-7 >= 1 is false) *)
      specialize (H_dec 3%nat 4%nat).
      simpl in H_dec.
      assert (H_bounds : (0 <= 3 < 4)%nat /\ (4 < 6)%nat) by lia.
      destruct H_bounds as [H_range H_len].
      specialize (H_dec H_range H_len).
      lia.
Qed.