Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 1000.234 550.123 275125.864391.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.