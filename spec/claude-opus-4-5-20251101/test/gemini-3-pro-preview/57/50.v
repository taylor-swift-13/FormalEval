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

Example test_monotonic : monotonic_spec [3; 6; 2; 6; 7; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + unfold is_increasing in H_inc.
      specialize (H_inc 1%nat 2%nat).
      simpl in H_inc.
      assert (0 <= 1 < 2)%nat by lia.
      assert (2 < 6)%nat by (simpl; lia).
      specialize (H_inc H H0).
      simpl in H_inc.
      lia.
    + unfold is_decreasing in H_dec.
      specialize (H_dec 0%nat 1%nat).
      simpl in H_dec.
      assert (0 <= 0 < 1)%nat by lia.
      assert (1 < 6)%nat by (simpl; lia).
      specialize (H_dec H H0).
      simpl in H_dec.
      lia.
Qed.