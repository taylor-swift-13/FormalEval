
Require Import List.
Require Import ZArith.
Require Import PeanoNat.

Import ListNotations.

Definition compare_spec (game guess : list Z) (result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, i < length game ->
    nth i result 0 = Z.abs (nth i game 0 - nth i guess 0).
