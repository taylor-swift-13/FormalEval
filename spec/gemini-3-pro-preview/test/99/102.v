Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_60_00099900 : closest_integer_spec (-60.00099900) (-60).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-60)) with (-60) by (simpl; lra).
  replace (-60.00099900 - -60) with (-0.00099900) by lra.
  rewrite Rabs_left1 by lra.
  left.
  lra.
Qed.