Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 11.32261214198862 10.5 59.443713745440255.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.