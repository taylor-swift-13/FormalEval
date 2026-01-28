Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_9111_19 : closest_integer_spec (-9111.19) (-9111).
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR (-9111)) with (-9111) by (simpl; lra).
  replace (-9111.19 - (-9111)) with (-0.19) by lra.
  replace (Rabs (-0.19)) with 0.19 by (rewrite Rabs_left; lra).
  lra.
Qed.