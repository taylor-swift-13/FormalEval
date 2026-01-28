Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_decimal : closest_integer_spec (12345678900040000001 / 10000000000000000000) 1.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 1) with 1 by (simpl; lra).
  rewrite Rabs_right; lra.
Qed.