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

Example test_monotonic : monotonic_spec [] true.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction *)
    intros _.
    left. (* The empty list is increasing vacuously *)
    unfold is_increasing.
    intros i j H_range H_len.
    simpl in H_len.
    lia.
  - (* <- Direction *)
    intros _.
    reflexivity.
Qed.