Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_cyclic_shift (l1 l2 : list Z) : Prop :=
  exists part1 part2, l1 = part1 ++ part2 /\ l2 = part2 ++ part1.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> (exists l', is_cyclic_shift arr l' /\ Sorted Z.le l').

Example test_move_one_ball : move_one_ball_spec [3; 4; 5; 1; 2] true.
Proof.
  unfold move_one_ball_spec.
  split.
  - intros _.
    exists [1; 2; 3; 4; 5].
    split.
    + unfold is_cyclic_shift.
      exists [3; 4; 5], [1; 2].
      split; reflexivity.
    + repeat constructor; lia.
  - intros _. reflexivity.
Qed.