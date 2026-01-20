Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_3_6 : closest_integer_spec (36/10) 4%Z.
Proof.
  unfold closest_integer_spec.
  replace (IZR 4%Z) with 4 by (simpl; lra).
  replace (36 / 10 - 4) with (-4 / 10) by lra.
  replace (Rabs (-4 / 10)) with (4 / 10) by (rewrite Rabs_left; lra).
  left.
  lra.
Qed.