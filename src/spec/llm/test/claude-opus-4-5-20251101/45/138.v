Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 6.351228473089266e-51 1000000000000 3.175614236544633e-39.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.