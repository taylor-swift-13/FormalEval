Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_14_5 : closest_integer_spec (145/10) 15.
Proof.
  unfold closest_integer_spec.
  replace (IZR 15) with 15 by (simpl; lra).
  replace (145 / 10 - 15) with (- / 2) by lra.
  rewrite Rabs_Ropp.
  replace (Rabs (/ 2)) with (/ 2) by (rewrite Rabs_right; lra).
  right.
  split.
  - lra.
  - replace (Rabs 15) with 15 by (rewrite Rabs_right; lra).
    replace (Rabs (145 / 10)) with (145 / 10) by (rewrite Rabs_right; lra).
    lra.
Qed.