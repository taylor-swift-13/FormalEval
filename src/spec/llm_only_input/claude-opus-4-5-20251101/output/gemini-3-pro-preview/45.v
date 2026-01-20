Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition triangle_area_spec (a h : R) (res : R) : Prop :=
  res = a * h / 2.

Example triangle_area_test : triangle_area_spec 5 3 (15 / 2).
Proof.
  unfold triangle_area_spec.
  field.
Qed.