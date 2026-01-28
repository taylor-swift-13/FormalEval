Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_1 : closest_integer_spec (-87654321.12345) (-87654321).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-87654321)) with (-87654321) by (simpl; lra).
  left.
  unfold Rabs.
  destruct (Rcase_abs (-87654321.12345 - -87654321)); lra.
Qed.