
Require Import List.
Require Import Arith.

Definition move_one_ball_spec (arr : list nat) (result : bool) : Prop :=
  let sorted_arr := sort Nat.leb arr in
  result = true <-> (arr = sorted_arr \/ exists i, i > 0 /\ i < length arr /\ (skipn i arr ++ firstn i arr) = sorted_arr).
