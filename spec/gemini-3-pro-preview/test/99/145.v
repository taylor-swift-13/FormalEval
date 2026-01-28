Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_51_approx : closest_integer_spec (-51.278590000000001) (-51).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-51)) with (-51) by (simpl; lra).
  left.
  unfold Rabs.
  destruct (Rcase_abs (-51.278590000000001 - -51)); lra.
Qed.