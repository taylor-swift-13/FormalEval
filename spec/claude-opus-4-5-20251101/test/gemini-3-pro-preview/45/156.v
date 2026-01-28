Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 5.933203128831868 1000000000000 2966601564415.934.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.