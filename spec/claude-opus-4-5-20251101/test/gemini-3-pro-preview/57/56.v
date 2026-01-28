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

Example test_monotonic : monotonic_spec [3; -7; -11; -7; -11; -11] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + (* Prove not increasing using indices 0 and 1 *)
      unfold is_increasing in H_inc.
      specialize (H_inc 0%nat 1%nat).
      simpl in H_inc.
      assert (3 <= -7). { apply H_inc; lia. }
      lia.
    + (* Prove not decreasing using indices 2 and 3 *)
      unfold is_decreasing in H_dec.
      specialize (H_dec 2%nat 3%nat).
      simpl in H_dec.
      assert (-11 >= -7). { apply H_dec; lia. }
      lia.
Qed.