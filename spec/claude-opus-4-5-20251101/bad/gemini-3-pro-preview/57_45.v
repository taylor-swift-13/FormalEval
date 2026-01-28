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

Example test_monotonic : monotonic_spec [-7; -9; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true -> ... *)
    intros H. discriminate H.
  - (* <- Direction: is_increasing \/ is_decreasing -> false = true *)
    intros [H_inc | H_dec].
    + (* Case: Increasing *)
      (* Check indices 0 and 1: -7 and -9 *)
      specialize (H_inc 0 1).
      simpl in H_inc.
      (* H_inc implies -7 <= -9, which is false *)
      assert (-7 <= -9).
      { apply H_inc; lia. }
      lia.
    + (* Case: Decreasing *)
      (* Check indices 1 and 2: -9 and 1 *)
      specialize (H_dec 1 2).
      simpl in H_dec.
      (* H_dec implies -9 >= 1, which is false *)
      assert (-9 >= 1).
      { apply H_dec; lia. }
      lia.
Qed.