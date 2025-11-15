(* Given a positive floating point number, it can be decomposed into
and integer part (largest integer smaller than given number) and decimals
(leftover part always smaller than 1).

Return the decimal part of the number.
>>> truncate_number(3.5)
0.5 *)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Open Scope R_scope.

Definition truncate_number_pre(x : R) : Prop :=
  x > 0.

Definition truncate_number_spec (x frac : R) : Prop :=
  0 < x ->
  frac = x - IZR (floor x) /\
  0 <= frac < 1.
