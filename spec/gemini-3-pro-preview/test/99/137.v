Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_91_01 : closest_integer_spec (-91.01) (-91).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-91)) with (-91) by (simpl; lra).
  left.
  unfold Rabs.
  destruct (Rcase_abs (-91.01 - -91)); lra.
Qed.