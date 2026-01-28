Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_11_6 : closest_integer_spec (116/10) 12.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 12) with 12 by (simpl; lra).
  replace (116 / 10 - 12) with (-4 / 10) by lra.
  replace (Rabs (-4 / 10)) with (4 / 10).
  - lra.
  - rewrite Rabs_left; lra.
Qed.