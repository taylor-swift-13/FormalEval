Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 6.351228473089266e-51 1e+50 0.3175614236544633.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.