Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_1 : closest_integer_spec (IZR 1023456789000000000011101%Z / IZR 100000000000000000000000%Z) 10.
Proof.
  unfold closest_integer_spec.
  left.
  unfold Rabs.
  destruct (Rcase_abs (IZR 1023456789000000000011101%Z / IZR 100000000000000000000000%Z - IZR 10)).
  - lra.
  - lra.
Qed.