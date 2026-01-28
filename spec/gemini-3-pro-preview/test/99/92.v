Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_new : closest_integer_spec (90000009 + 999/1000) 90000010%Z.
Proof.
  unfold closest_integer_spec.
  left.
  replace (90000009 + 999 / 1000 - IZR 90000010%Z) with (- (1 / 1000)) by (simpl; lra).
  rewrite Rabs_Ropp.
  rewrite Rabs_right; lra.
Qed.