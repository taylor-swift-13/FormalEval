
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Definition sorted (l : list R) : Prop :=
  forall i j (Hi : i < length l) (Hj : j < length l) (Hle : i <= j),
    nth i l 0 <= nth j l 0.

Definition median_spec (l : list R) (m : R) : Prop :=
  sorted (sort (Rle_dec) l) /\
  let sorted_l := sort (Rle_dec) l in
  if Nat.odd (length l) then
    m = nth (length l / 2) sorted_l 0
  else
    m = (nth ((length l / 2) - 1) sorted_l 0 + nth (length l / 2) sorted_l 0) / 2.
