Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_10001 : closest_integer_spec 10001 10001.
Proof.
  unfold closest_integer_spec.
  replace (IZR 10001) with 10001 by (simpl; lra).
  replace (10001 - 10001) with 0 by lra.
  rewrite Rabs_R0.
  left.
  lra.
Qed.