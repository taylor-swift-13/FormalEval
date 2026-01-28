Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_6 : closest_integer_spec (-6) (-6).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-6)) with (-6) by (simpl; lra).
  replace (-6 - -6) with 0 by lra.
  rewrite Rabs_R0.
  left.
  lra.
Qed.