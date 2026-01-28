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

Lemma sqrt_600_bounds : 24.49 - /200 <= sqrt 600 /\ sqrt 600 < 24.49 + /200.
Proof.
  split.
  - apply Rle_trans with 24.485.
    + lra.
    + rewrite <- sqrt_square with (x := 24.485).
      * apply sqrt_le_1.
        -- lra.
        -- lra.
        -- lra.
      * lra.
  - apply Rlt_le_trans with 24.495.
    + rewrite <- sqrt_square with (x := 24.495).
      * apply sqrt_lt_1.
        -- lra.
        -- lra.
        -- lra.
      * lra.
    + lra.
Qed.

Example test_triangle_area : problem_71_spec 7 7 10 24.49.
Proof.
  unfold problem_71_spec.
  left.
  split.
  - unfold is_valid_triangle. lra.
  - unfold is_rounded_to_2_decimals, heron_area.
    split.
    + exists 2449%Z. simpl. lra.
    + assert (Harea: (7 + 7 + 10) / 2 * ((7 + 7 + 10) / 2 - 7) * ((7 + 7 + 10) / 2 - 7) * ((7 + 7 + 10) / 2 - 10) = 600) by lra.
      rewrite Harea.
      exact sqrt_600_bounds.
Qed.