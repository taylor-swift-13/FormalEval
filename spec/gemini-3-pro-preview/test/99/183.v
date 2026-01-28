Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_5_555 : closest_integer_spec 5.555 6.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 6) with 6 by (simpl; lra).
  unfold Rabs.
  destruct (Rcase_abs (5.555 - 6)).
  - lra.
  - lra.
Qed.