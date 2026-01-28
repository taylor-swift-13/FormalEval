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
  if Rlt_dec r 0 then truncate r else (truncate r + 1)%Z.

Definition standard_round (r : R) : Z :=
  if Rlt_dec (r - IZR (truncate r)) (1/2) then truncate r
  else (truncate r + 1)%Z.

Definition closest_integer_spec (value : R) (result : Z) : Prop :=
  (is_equidistant value -> result = round_away_from_zero value) /\
  (~is_equidistant value -> result = standard_round value).

Lemma up_neg_1_6 : up (-1.6) = (-1)%Z.
Proof.
  pose proof (archimed (-1.6)) as [H1 H2].
  assert (H_lower: IZR (-2) < IZR (up (-1.6))) by lra.
  assert (H_upper: IZR (up (-1.6)) < IZR 0) by lra.
  apply lt_IZR in H_lower.
  apply lt_IZR in H_upper.
  lia.
Qed.

Example test_neg_1_6 : closest_integer_spec (-1.6) (-2).
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate (-1.6) = (-2)%Z).
  {
    unfold truncate.
    rewrite up_neg_1_6.
    lia.
  }
  split.
  - intro H_eq.
    unfold is_equidistant in H_eq.
    rewrite H_trunc in H_eq.
    replace (IZR (-2)) with (-2) in H_eq by reflexivity.
    lra.
  - intro H_neq.
    unfold standard_round.
    rewrite H_trunc.
    replace (IZR (-2)) with (-2) by reflexivity.
    destruct (Rlt_dec (-1.6 - -2) (1/2)).
    + reflexivity.
    + exfalso. lra.
Qed.