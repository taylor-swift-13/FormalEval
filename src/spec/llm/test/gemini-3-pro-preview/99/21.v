Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_9_999 : closest_integer_spec 9.999 10.
Proof.
  unfold closest_integer_spec.
  replace (IZR 10) with 10 by (simpl; lra).
  replace 9.999 with (9999/1000) by lra.
  left.
  unfold Rabs.
  destruct (Rcase_abs (9999 / 1000 - 10)).
  - lra.
  - lra.
Qed.