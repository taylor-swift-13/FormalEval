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

Lemma up_15_3 : up (153/10) = 16%Z.
Proof.
  pose proof (archimed (153/10)) as [H1 H2].
  assert (H_lower: IZR 15 < IZR (up (153/10))) by lra.
  assert (H_upper: IZR (up (153/10)) < IZR 17) by lra.
  apply lt_IZR in H_lower.
  apply lt_IZR in H_upper.
  lia.
Qed.

Example test_15_3 : closest_integer_spec (153/10) 15.
Proof.
  unfold closest_integer_spec.
  assert (H_trunc: truncate (153/10) = 15%Z).
  {
    unfold truncate.
    rewrite up_15_3.
    destruct (Rlt_dec (153/10) 0); try lra.
    simpl. reflexivity.
  }
  split.
  - intro H_eq.
    unfold is_equidistant in H_eq.
    rewrite H_trunc in H_eq.
    assert (H_calc: Rabs (153/10 - IZR 15) = 3/10) by (rewrite Rabs_right; lra).
    rewrite H_calc in H_eq.
    lra.
  - intro H_neq.
    unfold standard_round.
    rewrite H_trunc.
    destruct (Rle_dec (153/10 - IZR 15) (1/2)).
    + reflexivity.
    + exfalso. lra.
Qed.