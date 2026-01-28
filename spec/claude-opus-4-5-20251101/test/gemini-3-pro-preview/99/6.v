Require Import Reals.
Require Import ZArith.
Require Import Floats.
Require Import Lra.
Require Import Lia.

Open Scope R_scope.

Definition floor (r : R) : Z := (up r - 1)%Z.

Definition round_away_from_zero (r : R) : Z :=
  if Rlt_dec r 0 then floor r else (floor r + 1)%Z.

Definition standard_round (r : R) : Z :=
  let f := floor r in
  let diff := r - IZR f in
  if Rlt_dec diff (1/2) then f
  else if Rgt_dec diff (1/2) then (f + 1)%Z
  else round_away_from_zero r.

Definition closest_integer_spec (value : R) (result : Z) : Prop :=
  result = standard_round value.

Lemma up_neg_2_8 : up (-2.8) = (-2)%Z.
Proof.
  pose proof (archimed (-2.8)) as [H1 H2].
  assert (H_bounds: IZR (-3) < IZR (up (-2.8)) /\ IZR (up (-2.8)) < IZR (-1)).
  {
    split; lra.
  }
  destruct H_bounds as [H_lower H_upper].
  apply lt_IZR in H_lower.
  apply lt_IZR in H_upper.
  lia.
Qed.

Example test_neg_2_8 : closest_integer_spec (-2.8) (-3).
Proof.
  unfold closest_integer_spec, standard_round, round_away_from_zero, floor.
  rewrite up_neg_2_8.
  simpl.
  destruct (Rlt_dec (-2.8 - IZR (-3)) (1 / 2)).
  - reflexivity.
  - exfalso. lra.
Qed.