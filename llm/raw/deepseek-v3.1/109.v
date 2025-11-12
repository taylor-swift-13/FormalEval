
Require Import List.
Require Import ZArith.
Require Import Bool.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  let sorted_arr := List.sort Z.le arr in
  if arr then
    result = true
  else
    result = List.existsb (fun i => arr ++ arr = sorted_arr) (seq 1 (length arr)) \/ arr = sorted_arr.
