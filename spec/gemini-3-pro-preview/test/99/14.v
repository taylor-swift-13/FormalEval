Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_99_99 : closest_integer_spec 99.99 100.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 100) with 100 by (simpl; lra).
  replace (99.99 - 100) with (-0.01) by lra.
  rewrite Rabs_left by lra.
  lra.
Qed.