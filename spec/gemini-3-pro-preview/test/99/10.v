Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_0_5 : closest_integer_spec 0.5 1.
Proof.
  unfold closest_integer_spec.
  right.
  replace (IZR 1) with 1 by (simpl; lra).
  replace (0.5 - 1) with (-0.5) by lra.
  replace (Rabs (-0.5)) with 0.5 by (unfold Rabs; destruct (Rcase_abs (-0.5)); lra).
  replace (Rabs 1) with 1 by (unfold Rabs; destruct (Rcase_abs 1); lra).
  replace (Rabs 0.5) with 0.5 by (unfold Rabs; destruct (Rcase_abs 0.5); lra).
  split; lra.
Qed.