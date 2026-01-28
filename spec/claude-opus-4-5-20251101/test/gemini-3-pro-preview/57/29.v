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

Example test_monotonic : monotonic_spec [-7; -9; 1; 5] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + (* Assume increasing, find contradiction at indices 0 and 1 *)
      unfold is_increasing in H_inc.
      specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (H_cond : (0 <= 0 < 1)%nat /\ (1 < 4)%nat).
      { split; lia. }
      destruct H_cond as [H1 H2].
      specialize (H_inc H1 H2).
      lia.
    + (* Assume decreasing, find contradiction at indices 1 and 2 *)
      unfold is_decreasing in H_dec.
      specialize (H_dec 1%nat 2%nat).
      simpl in H_dec.
      assert (H_cond : (0 <= 1 < 2)%nat /\ (2 < 4)%nat).
      { split; lia. }
      destruct H_cond as [H1 H2].
      specialize (H_dec H1 H2).
      lia.
Qed.