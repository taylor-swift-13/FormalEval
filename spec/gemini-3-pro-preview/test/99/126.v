Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_large_neg : closest_integer_spec (-187654321.123345) (-187654321).
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR (-187654321)) with (-187654321) by lra.
  replace (-187654321.123345 - -187654321) with (-0.123345) by lra.
  rewrite Rabs_left; lra.
Qed.