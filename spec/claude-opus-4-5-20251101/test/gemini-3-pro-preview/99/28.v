Require Import Reals.
Require Import ZArith.
Require Import Floats.
Require Import Lra.
Require Import Lia.

Open Scope R_scope.

Definition truncate (r : R) : Z := (up r - 1)%Z.

Definition is_equidistant (r : R) : Prop :=
  Rabs (r - IZR (truncate r)) = 1/2.

Definition round_away_from_zero (r : R) : Z :=
  if Rlt_dec r 0 then truncate r
  else (truncate r + 1)%Z.

Definition standard_round (r : R) : Z :=
  if Rle_dec (r - IZR (truncate r)) (1/2) then truncate r
  else (truncate r + 1)%Z.

Definition closest_integer_spec (value : R) (result : Z) : Prop :=
  (is_equidistant value -> result = round_away_from_zero value) /\
  (~is_equidistant value -> result = standard_round value).

Lemma up_neg_6 : up (-6) = (-5)%Z.
Proof.
  pose proof (archimed (-6)) as [H1 H2].
  assert (H_lower: IZR (-6) < IZR (up (-6))) by lra.
  assert (H_upper: IZR (up (-6)) <= IZR (-5)) by lra.
  apply lt_IZR in H_lower.
  apply le_IZR in H_upper.
  lia.
Qed.

Example test_neg_6 : closest_integer_spec (-6) (-6).
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate (-6) = (-6)%Z).
  {
    unfold truncate.
    rewrite up_neg_6.
    simpl. reflexivity.
  }
  split.
  - intro H_eq.
    unfold is_equidistant in H_eq.
    rewrite H_trunc in H_eq.
    replace (-6 - IZR (-6)) with 0 in H_eq by (simpl; lra).
    rewrite Rabs_R0 in H_eq.
    lra.
  - intro H_neq.
    unfold standard_round.
    rewrite H_trunc.
    destruct (Rle_dec (-6 - IZR (-6)) (1/2)).
    + reflexivity.
    + exfalso.
      replace (-6 - IZR (-6)) with 0 in n by (simpl; lra).
      lra.
Qed.