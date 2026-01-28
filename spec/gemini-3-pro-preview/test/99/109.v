Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_0_0000000009 : closest_integer_spec (9 / 10000000000) 0.
Proof.
  unfold closest_integer_spec.
  replace (IZR 0) with 0 by (simpl; lra).
  replace (9 / 10000000000 - 0) with (9 / 10000000000) by lra.
  rewrite Rabs_right.
  - left.
    lra.
  - lra.
Qed.