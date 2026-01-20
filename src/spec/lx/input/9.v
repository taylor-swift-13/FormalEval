(* """ From a given list of integers, generate a list of rolling maximum element found until given moment
in the sequence.
>>> rolling_max([1, 2, 3, 2, 3, 4, 2])
[1, 2, 3, 3, 3, 4, 4]
""" *)

(* Spec(input, output) :=

length(output) == length(input) ∧

∀i. 0 ≤ i < length(output) ∧
        (∀j. 0 ≤ j ≤ i → input[j] ≤ output[i]) ∧
        (∃j. 0 ≤ j ≤ i ∧ input[j] = output[i]) *)

Require Import List Arith.
Import ListNotations.

Definition Pre := True.

Definition Spec (input output : list nat) :=
  length output = length input /\
  forall i,
    i < length output ->
    (forall j, j <= i -> nth j input 0 <= nth i output 0) /\
    (exists j, j <= i /\ nth j input 0 = nth i output 0).

