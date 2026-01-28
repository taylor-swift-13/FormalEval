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

Lemma sqrt_264_bounds : 16.24 < sqrt 264 /\ sqrt 264 < 16.25.
Proof.
  split.
  - assert (H1: 16.24 * 16.24 = 263.7376) by lra.
    assert (H2: 263.7376 < 264) by lra.
    assert (H3: 0 <= 16.24) by lra.
    apply sqrt_lt_1.
    + lra.
    + lra.
    + lra.
  - assert (H1: 16.25 * 16.25 = 264.0625) by lra.
    assert (H2: 264 < 264.0625) by lra.
    assert (H3: 0 <= 264) by lra.
    rewrite <- (sqrt_square 16.25).
    + apply sqrt_lt_1.
      * lra.
      * assert (0 <= 16.25) by lra. 
        rewrite <- (sqrt_square 16.25); [|lra].
        apply sqrt_pos.
      * lra.
    + lra.
Qed.

Example test_triangle_area : problem_71_spec 10 5 7 16.25.
Proof.
  unfold problem_71_spec.
  left.
  split.
  - unfold is_valid_triangle. lra.
  - unfold is_rounded_to_2_decimals, heron_area.
    split.
    + exists 1625%Z. simpl. lra.
    + assert (Harea: (10 + 5 + 7) / 2 * ((10 + 5 + 7) / 2 - 10) * ((10 + 5 + 7) / 2 - 5) * ((10 + 5 + 7) / 2 - 7) = 264) by lra.
      rewrite Harea.
      destruct sqrt_264_bounds as [Hlb Hub].
      lra.
Qed.