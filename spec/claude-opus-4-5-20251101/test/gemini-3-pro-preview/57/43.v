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

Example test_monotonic : monotonic_spec [5; 1; -10; -9; 1; 2; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + (* Disprove increasing: 5 <= 1 is false *)
      unfold is_increasing in H_inc.
      specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (H_range : (0 <= 0 < 1)%nat) by lia.
      assert (H_len : (1 < 7)%nat) by (simpl; lia).
      specialize (H_inc H_range H_len).
      simpl in H_inc.
      lia.
    + (* Disprove decreasing: -10 >= -9 is false *)
      unfold is_decreasing in H_dec.
      specialize (H_dec 2%nat 3%nat).
      simpl in H_dec.
      assert (H_range : (0 <= 2 < 3)%nat) by lia.
      assert (H_len : (3 < 7)%nat) by (simpl; lia).
      specialize (H_dec H_range H_len).
      simpl in H_dec.
      lia.
Qed.