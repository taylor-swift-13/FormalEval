Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_closest_integer_10 : closest_integer_spec 10 10%Z.
Proof.
  unfold closest_integer_spec.
  left.
  simpl.
  replace (10 - 10) with 0 by ring.
  rewrite Rabs_R0.
  apply Rinv_0_lt_compat.
  lra.
Qed.