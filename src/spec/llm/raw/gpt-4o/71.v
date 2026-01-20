
Require Import Reals.
Require Import Psatz.

Definition triangle_area_spec (a b c : R) (area : R) : Prop :=
  (a + b <= c \/ a + c <= b \/ b + c <= a -> area = -1) /\
  (a + b > c /\ a + c > b /\ b + c > a ->
   let p := (a + b + c) / 2 in
   area = round ((p * (p - a) * (p - b) * (p - c)) ^ 0.5) 2).
