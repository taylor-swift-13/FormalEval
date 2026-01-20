
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Div2.

Definition median_spec (l : list nat) (result : nat) : Prop :=
  exists sorted_l : list nat,
    sorted_l = Nat.sort l /\
    if Nat.even (length l) then
      result = (nth (div2 (length l) - 1) sorted_l 0 + nth (div2 (length l)) sorted_l 0) / 2
    else
      result = nth (div2 (length l)) sorted_l 0.
