
Require Import Coq.Reals.Reals.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = a * h / 2.
