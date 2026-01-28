Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_6_65 : closest_integer_spec (-6.65) (-7).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-7)) with (-7) by (simpl; lra).
  replace (-6.65 - -7) with 0.35 by lra.
  replace (Rabs 0.35) with 0.35 by (rewrite Rabs_right; lra).
  left.
  lra.
Qed.