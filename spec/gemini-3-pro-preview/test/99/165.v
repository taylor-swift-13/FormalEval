Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_10_00001 : closest_integer_spec (1000001 / 100000) 10.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 10) with 10 by (simpl; lra).
  replace (1000001 / 100000 - 10) with (1 / 100000) by lra.
  rewrite Rabs_right; lra.
Qed.