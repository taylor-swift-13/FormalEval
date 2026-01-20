
Require Import Reals.
Require Import Floats.
Open Scope R_scope.

Definition is_valid_triangle (a b c : R) : Prop :=
  a + b > c /\ a + c > b /\ b + c > a.

Definition heron_area (a b c : R) : R :=
  let p := (a + b + c) / 2 in
  sqrt (p * (p - a) * (p - b) * (p - c)).

Definition round_to_2_decimals (x : R) : R :=
  (IZR (up (x * 100 - /2))) / 100.

Definition triangle_area_spec (a b c : R) (result : R) : Prop :=
  (is_valid_triangle a b c -> result = round_to_2_decimals (heron_area a b c)) /\
  (~is_valid_triangle a b c -> result = -1).
