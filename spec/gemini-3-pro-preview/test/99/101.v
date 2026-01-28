Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_90900 : closest_integer_spec 90900 90900.
Proof.
  unfold closest_integer_spec.
  replace (IZR 90900) with 90900 by (simpl; lra).
  replace (90900 - 90900) with 0 by lra.
  rewrite Rabs_R0.
  left.
  lra.
Qed.