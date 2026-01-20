Require Import Reals.
Require Import ZArith.
Require Import Floats.
Require Import Psatz. (* For lra and lia tactics *)

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

(* Helper lemma to determine the value of up 10 *)
Lemma up_10 : up 10 = 11%Z.
Proof.
  pose proof (archimed 10) as [H1 H2].
  (* We know 10 < IZR (up 10) <= 11 *)
  assert (H_bounds: 10 < IZR (up 10) <= 11) by lra.
  destruct H_bounds as [H_lt H_le].
  apply lt_IZR in H_lt.
  apply le_IZR in H_le.
  lia.
Qed.

(* Helper lemma to calculate truncate 10 *)
Lemma truncate_10 : truncate 10 = 10%Z.
Proof.
  unfold truncate.
  destruct (Rlt_dec 10 0) as [H_neg | H_nonneg].
  - (* Case 10 < 0: Contradiction *)
    lra.
  - (* Case 10 >= 0 *)
    rewrite up_10.
    (* Calculate Z.of_nat (Z.abs_nat (11 - 1)) *)
    replace (11 - 1)%Z with 10%Z by lia.
    simpl.
    reflexivity.
Qed.

Example test_case_1 : closest_integer_spec 10 10%Z.
Proof.
  unfold closest_integer_spec.
  split.
  - (* Case: is_equidistant 10 -> ... *)
    intro H_equi.
    unfold is_equidistant in H_equi.
    rewrite truncate_10 in H_equi.
    (* Rabs (10 - 10) = 0 *)
    replace (10 - IZR 10) with 0 in H_equi by lra.
    rewrite Rabs_R0 in H_equi.
    (* 0 = 1/2 is false *)
    lra.
  - (* Case: ~is_equidistant 10 -> 10 = standard_round 10 *)
    intro H_not_equi.
    unfold standard_round.
    rewrite truncate_10.
    (* Check condition: 10 - 10 <= 1/2 *)
    destruct (Rle_dec (10 - IZR 10) (1/2)) as [H_le | H_gt].
    + (* Condition holds *)
      reflexivity.
    + (* Condition fails: Contradiction *)
      replace (10 - IZR 10) with 0 in H_gt by lra.
      lra.
Qed.