Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_6_000999900 : closest_integer_spec (-6.000999900) (-6).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-6)) with (-6) by (simpl; lra).
  replace (-6.000999900 - -6) with (-0.000999900) by lra.
  left.
  rewrite Rabs_left; lra.
Qed.