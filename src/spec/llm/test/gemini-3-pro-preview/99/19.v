Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_99_9999 : closest_integer_spec (999999 / 10000) 100.
Proof.
  unfold closest_integer_spec.
  replace (IZR 100) with 100 by (simpl; lra).
  left.
  replace (999999 / 10000 - 100) with (- (1 / 10000)) by lra.
  rewrite Rabs_Ropp.
  rewrite Rabs_right; [|lra].
  lra.
Qed.