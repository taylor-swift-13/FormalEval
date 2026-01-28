Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_54_9999 : closest_integer_spec (-54.9999) (-55).
Proof.
  unfold closest_integer_spec.
  left.
  replace (-54.9999 - IZR (-55)) with (1/10000) by (simpl; lra).
  rewrite Rabs_right; lra.
Qed.