Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_new : closest_integer_spec (-78765432112345 / 100000) (-787654321)%Z.
Proof.
  unfold closest_integer_spec.
  left.
  replace (-78765432112345 / 100000 - IZR (-787654321)%Z) with (-12345 / 100000) by lra.
  rewrite Rabs_left by lra.
  lra.
Qed.