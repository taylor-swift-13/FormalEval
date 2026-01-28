Require Import Reals.
Require Import ZArith.
Require Import Floats.
Require Import Lra.
Require Import Lia.

Open Scope R_scope.

Definition truncate (r : R) : Z :=
  if Rlt_dec r 0 then Z.of_nat (S (Z.abs_nat (up r - 1)))
  else Z.of_nat (Z.abs_nat (up r - 1)).

Definition is_equidistant (r : R) : Prop :=
  Rabs (r - IZR (truncate r)) = 1/2.

Definition round_away_from_zero (r : R) : Z :=
  if Rlt_dec r 0 then (truncate r - 1)%Z
  else (truncate r + 1)%Z.

Definition standard_round (r : R) : Z :=
  if Rle_dec (r - IZR (truncate r)) (1/2) then truncate r
  else if Rlt_dec r 0 then (truncate r - 1)%Z
  else (truncate r + 1)%Z.

Definition closest_integer_spec (value : R) (result : Z) : Prop :=
  (is_equidistant value -> result = round_away_from_zero value) /\
  (~is_equidistant value -> result = standard_round value).

Lemma up_5_5 : up 5.5 = 6%Z.
Proof.
  pose proof (archimed 5.5) as [H1 H2].
  assert (H_lower: 5 < IZR (up 5.5)) by lra.
  assert (H_upper: IZR (up 5.5) < 7) by lra.
  apply lt_IZR in H_lower.
  apply lt_IZR in H_upper.
  lia.
Qed.

Example test_5_5 : closest_integer_spec 5.5 6.
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate 5.5 = 5%Z).
  {
    unfold truncate.
    rewrite up_5_5.
    destruct (Rlt_dec 5.5 0); try lra.
    simpl. reflexivity.
  }
  split.
  - intro H_eq.
    unfold round_away_from_zero.
    rewrite H_trunc.
    destruct (Rlt_dec 5.5 0); try lra.
    reflexivity.
  - intro H_neq.
    exfalso. apply H_neq.
    unfold is_equidistant.
    rewrite H_trunc.
    replace (5.5 - IZR 5) with (1/2) by lra.
    rewrite Rabs_pos_eq; lra.
Qed.