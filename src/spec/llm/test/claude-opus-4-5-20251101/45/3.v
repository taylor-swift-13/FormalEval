Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 10 8 40.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.