Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec (6.351228473089266 * / 10^51) 1000000000000 (3.175614236544633 * / 10^39).
Proof.
  unfold triangle_area_spec.
  replace 1000000000000 with (10^12) by lra.
  field_simplify; try lra;
  repeat apply mult_neq_0; try lra; apply pow_nonzero; lra.
Qed.