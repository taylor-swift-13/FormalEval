
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import ZArith.Zabs.

Definition compare_spec (game guess : list Z) (result : list Z) : Prop :=
  length result = length game /\
  length game = length guess /\
  (forall i : nat, (i < length game)%nat ->
   nth i result 0 = Z.abs (nth i game 0 - nth i guess 0)).
