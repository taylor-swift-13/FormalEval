Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_9999_99 : closest_integer_spec (999999 / 100) 10000.
Proof.
  unfold closest_integer_spec.
  replace (IZR 10000) with 10000 by lra.
  replace (999999 / 100 - 10000) with (- (1 / 100)) by lra.
  rewrite Rabs_Ropp.
  rewrite Rabs_right by lra.
  left.
  lra.
Qed.