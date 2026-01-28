Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec (1 / 10^50) (1 / 10^50) (5 / 10^101).
Proof.
  unfold triangle_area_spec.
  field; try apply pow_nonzero; lra.
Qed.