Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_5 : closest_integer_spec 5 5.
Proof.
  unfold closest_integer_spec.
  replace (IZR 5) with 5 by (simpl; lra).
  replace (5 - 5) with 0 by lra.
  rewrite Rabs_R0.
  left.
  lra.
Qed.