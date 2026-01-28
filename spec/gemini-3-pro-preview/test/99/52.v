Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_9112 : closest_integer_spec (-9111.6919) (-9112).
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR (-9112)) with (-9112) by (simpl; lra).
  unfold Rabs.
  destruct (Rcase_abs (-9111.6919 - -9112)); lra.
Qed.