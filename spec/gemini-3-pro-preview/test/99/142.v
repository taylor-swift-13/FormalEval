Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_11_99 : closest_integer_spec (1199/100) 12.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 12) with 12 by (simpl; lra).
  unfold Rabs.
  destruct (Rcase_abs (1199 / 100 - 12)); lra.
Qed.