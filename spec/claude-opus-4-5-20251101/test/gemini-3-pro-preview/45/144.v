Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 5.594645686633063%R 5.933203128831868%R ((5.594645686633063 * 5.933203128831868) / 2)%R.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.