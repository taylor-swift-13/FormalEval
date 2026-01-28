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

Example test_monotonic : monotonic_spec [1; 1; 1; 1; 2; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + unfold is_increasing in H_inc.
      specialize (H_inc 4%nat 5%nat).
      simpl in H_inc.
      assert (H_bounds : (0 <= 4 < 5)%nat /\ (5 < 8)%nat) by lia.
      destruct H_bounds as [H1 H2].
      specialize (H_inc H1 H2).
      lia.
    + unfold is_decreasing in H_dec.
      specialize (H_dec 3%nat 4%nat).
      simpl in H_dec.
      assert (H_bounds : (0 <= 3 < 4)%nat /\ (4 < 8)%nat) by lia.
      destruct H_bounds as [H1 H2].
      specialize (H_dec H1 H2).
      lia.
Qed.