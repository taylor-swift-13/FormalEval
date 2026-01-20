
Require Import Reals.
Require Import Lra.

Definition triangle_area_spec (a b c : R) (result : R) : Prop :=
  if (a + b <=? c) || (a + c <=? b) || (b + c <=? a) then
    result = -1
  else
    let p := (a + b + c) / 2 in
    result = round (sqrt (p * (p - a) * (p - b) * (p - c))) 2.
