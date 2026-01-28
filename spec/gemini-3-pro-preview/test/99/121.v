Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_4_9999 : closest_integer_spec 4.9999 5.
Proof.
  unfold closest_integer_spec.
  replace (IZR 5) with 5 by (simpl; lra).
  replace (4.9999 - 5) with (-0.0001) by lra.
  left.
  unfold Rabs.
  destruct (Rcase_abs (-0.0001)); lra.
Qed.