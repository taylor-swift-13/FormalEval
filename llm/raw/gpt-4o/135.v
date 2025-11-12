
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition can_arrange_spec (arr : list nat) (index : nat) : Prop :=
  (index = -1 /\ forall i, 1 <= i < length arr -> arr[i] >= arr[i - 1]) \/
  (1 <= index < length arr /\ arr[index] < arr[index - 1] /\
   forall i, index < i < length arr -> arr[i] >= arr[i - 1]).
