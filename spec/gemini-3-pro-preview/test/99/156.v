Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_599_5 : closest_integer_spec (-599.5) (-600).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-600)) with (-600) by (simpl; lra).
  replace (-599.5 - -600) with 0.5 by lra.
  replace (/ 2) with 0.5 by lra.
  right.
  split.
  - unfold Rabs.
    destruct (Rcase_abs 0.5); lra.
  - unfold Rabs.
    destruct (Rcase_abs (-600)); destruct (Rcase_abs (-599.5)); lra.
Qed.