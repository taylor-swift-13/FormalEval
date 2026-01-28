Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_111_9 : closest_integer_spec (-111.900090099990900) (-112).
Proof.
  unfold closest_integer_spec.
  replace (IZR (-112)) with (-112) by (simpl; lra).
  left.
  unfold Rabs.
  destruct (Rcase_abs (-111.900090099990900 - -112)); lra.
Qed.