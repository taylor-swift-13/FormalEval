
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.

Definition median_spec (l : list nat) (median : R) : Prop :=
  exists sorted_l,
    Permutation sorted_l l /\
    sorted_l = sort Nat.leb l /\
    (length l mod 2 = 1 -> median = INR (nth (length l / 2) sorted_l 0)) /\
    (length l mod 2 = 0 -> median = (INR (nth (length l / 2 - 1) sorted_l 0) + INR (nth (length l / 2) sorted_l 0)) / 2).
