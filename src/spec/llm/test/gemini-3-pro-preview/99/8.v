Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_5_5 : closest_integer_spec 5.5 6.
Proof.
  unfold closest_integer_spec.
  replace (IZR 6) with 6 by (simpl; lra).
  replace (5.5 - 6) with (-0.5) by lra.
  replace (/ 2) with 0.5 by lra.
  right.
  split.
  - unfold Rabs.
    destruct (Rcase_abs (-0.5)); lra.
  - unfold Rabs.
    destruct (Rcase_abs 6); destruct (Rcase_abs 5.5); lra.
Qed.