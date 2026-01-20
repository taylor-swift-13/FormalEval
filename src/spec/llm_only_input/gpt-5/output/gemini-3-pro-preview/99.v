Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example closest_integer_spec_example_10 :
  closest_integer_spec (IZR 10%Z) 10%Z.
Proof.
  unfold closest_integer_spec.
  left.
  simpl.
  replace (IZR 10%Z - IZR 10%Z) with 0 by lra.
  rewrite Rabs_R0.
  lra.
Qed.