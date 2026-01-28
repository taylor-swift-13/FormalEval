Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_1 : closest_integer_spec (9999009909099 / 100) 99990099091.
Proof.
  unfold closest_integer_spec.
  left.
  replace (IZR 99990099091) with (9999009909100 / 100) by (field; lra).
  replace (9999009909099 / 100 - 9999009909100 / 100) with ((9999009909099 - 9999009909100) / 100) by (field; lra).
  replace (9999009909099 - 9999009909100) with (-1) by lra.
  replace (Rabs ((-1) / 100)) with (1 / 100).
  - lra.
  - replace ((-1) / 100) with (- (1 / 100)) by field.
    rewrite Rabs_Ropp.
    rewrite Rabs_right; lra.
Qed.