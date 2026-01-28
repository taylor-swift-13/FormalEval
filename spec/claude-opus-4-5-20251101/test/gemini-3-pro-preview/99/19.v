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

Lemma up_99_9999 : up 99.9999 = 100%Z.
Proof.
  pose proof (archimed 99.9999) as [H1 H2].
  assert (H_lower: IZR 99 < IZR (up 99.9999)) by lra.
  assert (H_upper: IZR (up 99.9999) < IZR 101) by lra.
  apply lt_IZR in H_lower.
  apply lt_IZR in H_upper.
  lia.
Qed.

Example test_99_9999 : closest_integer_spec 99.9999 100.
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate 99.9999 = 99%Z).
  {
    unfold truncate.
    rewrite up_99_9999.
    destruct (Rlt_dec 99.9999 0); try lra.
    simpl. reflexivity.
  }
  split.
  - intro H_eq.
    unfold is_equidistant in H_eq.
    rewrite H_trunc in H_eq.
    replace (99.9999 - IZR 99) with 0.9999 in H_eq by (simpl; lra).
    rewrite Rabs_right in H_eq by lra.
    lra.
  - intro H_neq.
    unfold standard_round.
    rewrite H_trunc.
    destruct (Rle_dec (99.9999 - IZR 99) (1/2)).
    + exfalso.
      replace (99.9999 - IZR 99) with 0.9999 in r by (simpl; lra).
      lra.
    + destruct (Rlt_dec 99.9999 0).
      * lra.
      * reflexivity.
Qed.