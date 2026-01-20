Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_90109111_6919 : closest_integer_spec (-90109111.6919) (-90109112).
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR (-90109112)) with (-90109112) by (simpl; lra).
  replace (-90109111.6919 - -90109112) with 0.3081 by lra.
  rewrite Rabs_pos_eq; lra.
Qed.