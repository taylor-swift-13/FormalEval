Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 1000000000000 999999999999 (4.999999999995e23).
Proof.
  unfold triangle_area_spec.
  lra.
Qed.