Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_1_6 : closest_integer_spec (-1.6) (-2).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-2)) with (-2) by (simpl; lra).
  replace (-1.6 - -2) with 0.4 by lra.
  rewrite Rabs_pos_eq by lra.
  left.
  lra.
Qed.