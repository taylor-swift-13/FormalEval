
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.

Definition compare_spec (game guess result : list nat) : Prop :=
  length game = length guess /\
  length game = length result /\
  forall i, i < length game ->
    nth i result 0 = Nat.abs (nth i game 0 - nth i guess 0).
