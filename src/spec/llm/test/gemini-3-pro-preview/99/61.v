Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_999000_999 : closest_integer_spec 999000.999 999001.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 999001) with 999001 by (simpl; lra).
  rewrite Rabs_left.
  - lra.
  - lra.
Qed.