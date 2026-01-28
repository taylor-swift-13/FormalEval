Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_new : closest_integer_spec (-87654321.212345) (-87654321).
Proof.
  unfold closest_integer_spec.
  left.
  replace (-87654321.212345) with (-87654321212345 / 1000000) by lra.
  replace (IZR (-87654321)) with (-87654321) by (simpl; lra).
  replace (-87654321212345 / 1000000 - -87654321) with (-212345 / 1000000) by lra.
  rewrite Rabs_left; lra.
Qed.