Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_9111_699 : closest_integer_spec (-9111699 / 1000) (-9112)%Z.
Proof.
  unfold closest_integer_spec.
  replace (IZR (-9112)%Z) with (-9112) by (simpl; lra).
  left.
  replace (-9111699 / 1000 - -9112) with (301 / 1000) by lra.
  rewrite Rabs_right; lra.
Qed.