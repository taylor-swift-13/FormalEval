Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_911_99 : closest_integer_spec 911.99 912.
Proof.
  unfold closest_integer_spec.
  replace (IZR 912) with 912 by (simpl; lra).
  replace (911.99 - 912) with (-0.01) by lra.
  left.
  assert (H: Rabs (-0.01) = 0.01).
  { unfold Rabs. destruct (Rcase_abs (-0.01)); lra. }
  rewrite H.
  lra.
Qed.