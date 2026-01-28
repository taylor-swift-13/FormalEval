Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_cyclic_shift (l1 l2 : list Z) : Prop :=
  exists part1 part2, l1 = part1 ++ part2 /\ l2 = part2 ++ part1.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> (exists l', is_cyclic_shift arr l' /\ Sorted Z.le l').

Example test_move_one_ball : move_one_ball_spec [4%Z; 1%Z] true.
Proof.
  unfold move_one_ball_spec.
  split.
  - intros _.
    exists [1%Z; 4%Z].
    split.
    + unfold is_cyclic_shift.
      exists [4%Z], [1%Z].
      split.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + repeat (constructor; try lia).
  - intros _.
    reflexivity.
Qed.