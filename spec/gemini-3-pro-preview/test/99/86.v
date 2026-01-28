Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_0_9096 : closest_integer_spec (9096 / 10000) 1%Z.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 1%Z) with 1 by (simpl; lra).
  assert (H: 9096 / 10000 - 1 = -904 / 10000) by lra.
  rewrite H.
  rewrite Rabs_left.
  - lra.
  - lra.
Qed.