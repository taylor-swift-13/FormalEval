Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 3.0140143224731513 3.7763622848915785 ((3.0140143224731513 * 3.7763622848915785) / 2).
Proof.
  unfold triangle_area_spec.
  lra.
Qed.