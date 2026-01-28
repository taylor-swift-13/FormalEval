Require Import Reals.
Require Import ZArith.
Require Import Lra.
Open Scope R_scope.

Definition is_valid_triangle (a b c : R) : Prop :=
  a > 0 /\ b > 0 /\ c > 0 /\
  a + b > c /\ a + c > b /\ b + c > a.

Definition heron_area (a b c : R) : R :=
  let s := (a + b + c) / 2 in
  sqrt (s * (s - a) * (s - b) * (s - c)).

Definition is_rounded_to_2_decimals (rounded_val original_val : R) : Prop :=
  (exists z : Z, rounded_val = IZR z / 100) /\
  rounded_val - /200 <= original_val /\ original_val < rounded_val + /200.

Definition problem_71_pre (a b c : R) : Prop := True.

Definition problem_71_spec (a b c : R) (ret : R) : Prop :=
  (is_valid_triangle a b c /\ is_rounded_to_2_decimals ret (heron_area a b c))
  \/
  (~ (is_valid_triangle a b c) /\ ret = -1).

Lemma sqrt_3600 : sqrt 3600 = 60.
Proof.
  rewrite <- (sqrt_square 60).
  - f_equal. lra.
  - lra.
Qed.

Example test_triangle_area : problem_71_spec 8 15 17 60.
Proof.
  unfold problem_71_spec.
  left.
  split.
  - unfold is_valid_triangle. lra.
  - unfold is_rounded_to_2_decimals, heron_area.
    split.
    + exists 6000%Z. simpl. lra.
    + assert (Harea: (8 + 15 + 17) / 2 * ((8 + 15 + 17) / 2 - 8) * ((8 + 15 + 17) / 2 - 15) * ((8 + 15 + 17) / 2 - 17) = 3600) by lra.
      rewrite Harea.
      rewrite sqrt_3600.
      lra.
Qed.