Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_99_9 : closest_integer_spec 99.9 100.
Proof.
  unfold closest_integer_spec.
  replace (IZR 100) with 100 by (simpl; lra).
  replace (99.9 - 100) with (-0.1) by lra.
  replace (Rabs (-0.1)) with 0.1 by (rewrite Rabs_left; lra).
  left.
  lra.
Qed.