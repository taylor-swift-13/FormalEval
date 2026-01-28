Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 1e+50 1e+50 5e+99.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.