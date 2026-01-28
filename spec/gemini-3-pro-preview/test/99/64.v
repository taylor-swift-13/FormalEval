Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_new : closest_integer_spec (-901091116919999 / 10000000) (-90109112).
Proof.
  unfold closest_integer_spec.
  left.
  replace (-901091116919999 / 10000000 - IZR (-90109112)) with (3080001 / 10000000) by (field_simplify; lra).
  rewrite Rabs_right; lra.
Qed.