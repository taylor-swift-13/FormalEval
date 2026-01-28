Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_10_2345678900000000001 : closest_integer_spec 10.2345678900000000001 10.
Proof.
  unfold closest_integer_spec.
  replace (IZR 10) with 10 by (simpl; lra).
  left.
  rewrite Rabs_right; lra.
Qed.