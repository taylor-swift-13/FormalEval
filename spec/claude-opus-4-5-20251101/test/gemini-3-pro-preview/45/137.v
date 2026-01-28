Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 500000001 1000000000000 2.500000005e+20.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.