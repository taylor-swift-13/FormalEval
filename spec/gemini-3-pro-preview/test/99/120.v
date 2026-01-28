Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_87654321_123345 : closest_integer_spec (-87654321123345 / 1000000) (-87654321)%Z.
Proof.
  unfold closest_integer_spec.
  left.
  replace (-87654321123345 / 1000000 - IZR (-87654321)%Z) with (-123345 / 1000000) by lra.
  rewrite Rabs_left; lra.
Qed.