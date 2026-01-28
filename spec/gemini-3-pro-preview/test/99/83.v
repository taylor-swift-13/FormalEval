Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_9900 : closest_integer_spec (-9900) (-9900).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-9900)) with (-9900) by (simpl; lra).
  replace (-9900 - -9900) with 0 by lra.
  rewrite Rabs_R0.
  left.
  lra.
Qed.