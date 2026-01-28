Require Import Reals.
Require Import ZArith.
Require Import Floats.
Require Import Lra.
Require Import Lia.

Open Scope R_scope.

Definition truncate (r : R) : Z := (up r - 1)%Z.

Definition is_equidistant (r : R) : Prop :=
  r - IZR (truncate r) = 1/2.

Definition round_away_from_zero (r : R) : Z :=
  if Rlt_dec r 0 then truncate r
  else (truncate r + 1)%Z.

Definition standard_round (r : R) : Z :=
  if Rlt_dec (r - IZR (truncate r)) (1/2) then truncate r
  else (truncate r + 1)%Z.

Definition closest_integer_spec (value : R) (result : Z) : Prop :=
  (is_equidistant value -> result = round_away_from_zero value) /\
  (~is_equidistant value -> result = standard_round value).

Lemma up_neg_99_9 : up (-999/10) = (-99)%Z.
Proof.
  pose proof (archimed (-999/10)) as [H1 H2].
  assert (H_up_lt_m98: IZR (up (-999/10)) < -98).
  {
    lra.
  }
  apply lt_IZR in H_up_lt_m98.
  assert (H_up_gt_m100: IZR (up (-999/10)) > -100).
  {
    lra.
  }
  apply lt_IZR in H_up_gt_m100.
  lia.
Qed.

Example test_neg_99_9 : closest_integer_spec (-999/10) (-100).
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate (-999/10) = (-100)%Z).
  {
    unfold truncate.
    rewrite up_neg_99_9.
    simpl. reflexivity.
  }
  split.
  - intro H_eq.
    unfold is_equidistant in H_eq.
    rewrite H_trunc in H_eq.
    replace (-999 / 10 - IZR (-100)) with (1/10) in H_eq by (simpl; lra).
    lra.
  - intro H_neq.
    unfold standard_round.
    rewrite H_trunc.
    destruct (Rlt_dec (-999 / 10 - IZR (-100)) (1 / 2)).
    + reflexivity.
    + exfalso.
      replace (-999 / 10 - IZR (-100)) with (1/10) in n by (simpl; lra).
      lra.
Qed.