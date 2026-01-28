Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  Rabs (area - (a * h) / 2) < 0.0001.

Example test_triangle_area : triangle_area_spec 2.5171570275185937 2.5171570275185937 3.1680397505931213.
Proof.
  unfold triangle_area_spec.
  unfold Rabs.
  match goal with
  | |- context [Rcase_abs ?x] => destruct (Rcase_abs x)
  end; lra.
Qed.