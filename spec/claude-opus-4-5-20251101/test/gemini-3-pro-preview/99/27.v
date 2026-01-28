Require Import Reals.
Require Import ZArith.
Require Import Floats.
Require Import Lra.
Require Import Lia.

Open Scope R_scope.

Definition truncate (r : R) : Z := (up r) - 1.

Definition is_equidistant (r : R) : Prop :=
  (r - IZR (truncate r)) = 1/2.

Definition round_away_from_zero (r : R) : Z :=
  if Rlt_dec r 0 then truncate r
  else (truncate r + 1)%Z.

Definition standard_round (r : R) : Z :=
  if Rle_dec (r - IZR (truncate r)) (1/2) then truncate r
  else (truncate r + 1)%Z.

Definition closest_integer_spec (value : R) (result : Z) : Prop :=
  (is_equidistant value -> result = round_away_from_zero value) /\
  (~is_equidistant value -> result = standard_round value).

Lemma up_neg_99 : up (-99) = (-98)%Z.
Proof.
  pose proof (archimed (-99)) as [H1 H2].
  assert (H_lower: IZR (-99) < IZR (up (-99))) by lra.
  assert (H_upper: IZR (up (-99)) <= IZR (-98)) by lra.
  apply lt_IZR in H_lower.
  apply le_IZR in H_upper.
  lia.
Qed.

Example test_neg_99 : closest_integer_spec (-99) (-99).
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate (-99) = (-99)%Z).
  {
    unfold truncate.
    rewrite up_neg_99.
    lia.
  }
  split.
  - intro H_eq.
    unfold is_equidistant in H_eq.
    rewrite H_trunc in H_eq.
    replace (-99 - IZR (-99)) with 0 in H_eq by (simpl; lra).
    lra.
  - intro H_neq.
    unfold standard_round.
    rewrite H_trunc.
    destruct (Rle_dec (-99 - IZR (-99)) (1/2)).
    + reflexivity.
    + exfalso.
      replace (-99 - IZR (-99)) with 0 in n by (simpl; lra).
      lra.
Qed.