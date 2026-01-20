Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_15_5 : closest_integer_spec (-15.5) (-16).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-16)) with (-16) by (simpl; lra).
  replace (-15.5 - -16) with 0.5 by lra.
  right.
  split.
  - replace (Rabs 0.5) with 0.5.
    + lra.
    + unfold Rabs. destruct (Rcase_abs 0.5); lra.
  - replace (Rabs (-16)) with 16.
    + replace (Rabs (-15.5)) with 15.5.
      * lra.
      * unfold Rabs. destruct (Rcase_abs (-15.5)); lra.
    + unfold Rabs. destruct (Rcase_abs (-16)); lra.
Qed.