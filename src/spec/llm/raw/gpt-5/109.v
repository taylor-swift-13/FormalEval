
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.

Open Scope Z_scope.

Definition rotate_left {A} (l : list A) (i : nat) : list A :=
  skipn i l ++ firstn i l.

Definition move_one_ball_spec (arr : list Z) (b : bool) : Prop :=
  b = true <-> (arr = nil \/ exists i, i < length arr /\ Sorted Z.le (rotate_left arr i)).
