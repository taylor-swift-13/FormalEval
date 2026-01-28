Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_900_999 : closest_integer_spec 900.999 901.
Proof.
  unfold closest_integer_spec.
  replace (IZR 901) with 901 by (simpl; lra).
  replace (900.999 - 901) with (-0.001) by lra.
  assert (H: Rabs (-0.001) = 0.001).
  { unfold Rabs. destruct (Rcase_abs (-0.001)); lra. }
  rewrite H.
  left.
  lra.
Qed.