Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_99999 : closest_integer_spec 99999 99999.
Proof.
  unfold closest_integer_spec.
  replace (IZR 99999) with 99999 by (simpl; lra).
  replace (99999 - 99999) with 0 by lra.
  rewrite Rabs_R0.
  left.
  lra.
Qed.