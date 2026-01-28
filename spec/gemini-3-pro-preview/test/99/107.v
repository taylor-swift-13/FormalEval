Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_decimal : closest_integer_spec (1234567854321 / 100000) 12345679.
Proof.
  unfold closest_integer_spec.
  left.
  unfold Rabs.
  destruct (Rcase_abs (1234567854321 / 100000 - IZR 12345679)); lra.
Qed.