Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_1_011 : closest_integer_spec (1011/1000) 1.
Proof.
  unfold closest_integer_spec.
  replace (IZR 1) with 1 by (simpl; lra).
  left.
  unfold Rabs.
  destruct (Rcase_abs (1011 / 1000 - 1)); lra.
Qed.