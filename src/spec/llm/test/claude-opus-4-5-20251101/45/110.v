Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec (1 / 1000000) 500000000 250.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.