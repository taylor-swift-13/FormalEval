Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_6999_99 : closest_integer_spec (-6999.99) (-7000).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-7000)) with (-7000) by (simpl; lra).
  replace (-6999.99 - -7000) with 0.01 by lra.
  rewrite Rabs_pos_eq by lra.
  left.
  lra.
Qed.