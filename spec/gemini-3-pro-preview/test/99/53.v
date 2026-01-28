Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_999_9999 : closest_integer_spec 999.9999 1000%Z.
Proof.
  unfold closest_integer_spec.
  left.
  unfold Rabs.
  destruct (Rcase_abs (999.9999 - IZR 1000%Z)); lra.
Qed.