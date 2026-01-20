Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_15_3 : closest_integer_spec 15.3 15.
Proof.
  unfold closest_integer_spec.
  replace (IZR 15) with 15 by (simpl; lra).
  left.
  replace (15.3 - 15) with 0.3 by lra.
  replace (/ 2) with 0.5 by lra.
  rewrite Rabs_right; lra.
Qed.