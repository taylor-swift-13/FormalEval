Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  Rabs (area - (a * h) / 2) < 0.0001.

Example test_triangle_area : triangle_area_spec 2.5171570275185937 2.654434753799174 3.3408145473075894.
Proof.
  unfold triangle_area_spec.
  apply Rabs_def1; lra.
Qed.