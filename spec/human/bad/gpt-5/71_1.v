Require Import Reals.
Require Import ZArith.
Require Import Lra.
Require Import R_sqrt.
Require Import Ring.
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

Definition  problem_71_spec (a b c : R) (ret : R) : Prop :=
  (is_valid_triangle a b c /\ is_rounded_to_2_decimals ret (heron_area a b c))
  \/
  (~ (is_valid_triangle a b c) /\ ret = -1).

Example triangle_area_example_3_4_5 :
  problem_71_spec (IZR 3%Z) (IZR 4%Z) (IZR 5%Z) 6%R.
Proof.
  unfold problem_71_spec.
  left. split.
  - unfold is_valid_triangle.
    repeat split; lra.
  - unfold is_rounded_to_2_decimals.
    split.
    + exists (600%Z). lra.
    + split.
      * unfold heron_area.
        replace ((IZR 3%Z + IZR 4%Z + IZR 5%Z) / 2) with 6 by lra.
        replace (6 - IZR 3%Z) with 3 by lra.
        replace (6 - IZR 4%Z) with 2 by lra.
        replace (6 - IZR 5%Z) with 1 by lra.
        assert (Hsqrt : sqrt (6 * 3 * 2 * 1) = 6).
        { apply sqrt_unique; [lra | ring]. }
        rewrite Hsqrt.
        lra.
      * unfold heron_area.
        replace ((IZR 3%Z + IZR 4%Z + IZR 5%Z) / 2) with 6 by lra.
        replace (6 - IZR 3%Z) with 3 by lra.
        replace (6 - IZR 4%Z) with 2 by lra.
        replace (6 - IZR 5%Z) with 1 by lra.
        assert (Hsqrt : sqrt (6 * 3 * 2 * 1) = 6).
        { apply sqrt_unique; [lra | ring]. }
        rewrite Hsqrt.
        lra.
Qed.