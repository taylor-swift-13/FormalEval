Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  Rabs (area - (a * h) / 2) < 1e-10.

Example test_triangle_area : triangle_area_spec 304.11337213124403 304.11337213124403 46242.471554518255.
Proof.
  unfold triangle_area_spec.
  unfold Rabs.
  destruct (Rcase_abs (46242.471554518255 - 304.11337213124403 * 304.11337213124403 / 2)); lra.
Qed.