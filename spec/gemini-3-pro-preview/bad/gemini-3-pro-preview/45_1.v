Require Import Coq.Reals.Reals.
Open Scope R_scope.

Definition triangle_area_spec (a h : R) (res : R) : Prop :=
  res = a * h / 2.

Example test_triangle_area : triangle_area_spec 5 3 7.5.
Proof.
  unfold triangle_area_spec.
  (* Replace decimal notation with fraction to assist the field tactic *)
  replace 7.5 with (75 / 10) by reflexivity.
  (* Solve the equation over the field of real numbers *)
  field.
  (* Prove that the denominators (2 and 10) are non-zero *)
  discrR.
Qed.