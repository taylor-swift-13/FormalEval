Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_11_9 : closest_integer_spec (119/10) 12.
Proof.
  unfold closest_integer_spec.
  left.
  replace (119 / 10 - IZR 12) with (-1 / 10) by (simpl; lra).
  rewrite Rabs_left; lra.
Qed.