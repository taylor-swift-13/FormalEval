Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_2_8 : closest_integer_spec (-28/10) (-3).
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR (-3)) with (-3) by (simpl; lra).
  replace (-28 / 10 - -3) with (2 / 10) by lra.
  rewrite Rabs_pos_eq by lra.
  lra.
Qed.