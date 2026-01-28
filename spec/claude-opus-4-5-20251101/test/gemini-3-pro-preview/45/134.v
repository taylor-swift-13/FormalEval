Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  Rabs (area - (a * h) / 2) < 1e-10.

Example test_triangle_area : triangle_area_spec 3.7763622848915785 550.123 1038.7318746257051.
Proof.
  unfold triangle_area_spec.
  unfold Rabs.
  match goal with
  | [ |- context[Rcase_abs ?e] ] => destruct (Rcase_abs e)
  end; lra.
Qed.