Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_6_9096 : closest_integer_spec (-69096 / 10000) (-7).
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR (-7)) with (-7) by (simpl; lra).
  replace (-69096 / 10000 - -7) with (904 / 10000) by lra.
  rewrite Rabs_right by lra.
  lra.
Qed.