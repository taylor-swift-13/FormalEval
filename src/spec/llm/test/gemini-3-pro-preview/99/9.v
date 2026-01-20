Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_neg_6_5 : closest_integer_spec (-6.5) (-7).
Proof.
  unfold closest_integer_spec.
  right.
  split.
  - replace (IZR (-7)) with (-7) by (simpl; lra).
    replace (-6.5 - -7) with 0.5 by lra.
    replace (/ 2) with 0.5 by lra.
    rewrite Rabs_pos_eq; lra.
  - replace (IZR (-7)) with (-7) by (simpl; lra).
    rewrite Rabs_left; try lra.
    rewrite Rabs_left; try lra.
Qed.