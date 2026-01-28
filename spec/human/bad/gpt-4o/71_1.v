Require Import Reals.
Require Import ZArith.
Require Import Psatz.
Open Scope R_scope.
Open Scope Z_scope.

(* Definition of a valid triangle *)
Definition is_valid_triangle (a b c : R) : Prop :=
  a > 0 /\ b > 0 /\ c > 0 /\
  a + b > c /\ a + c > b /\ b + c > a.

(* Heron's formula for area calculation *)
Definition heron_area (a b c : R) : R :=
  let s := (a + b + c) / 2 in
  sqrt (s * (s - a) * (s - b) * (s - c)).

(* Definition of rounding to 2 decimal places *)
Definition is_rounded_to_2_decimals (rounded_val original_val : R) : Prop :=
  (exists z : Z, rounded_val = IZR z / 100) /\
  rounded_val - /200 <= original_val /\ original_val < rounded_val + /200.

(* Specification definition *)
Definition problem_71_spec (a b c : R) (ret : R) : Prop :=
  (is_valid_triangle a b c /\ is_rounded_to_2_decimals ret (heron_area a b c))
  \/
  (~ (is_valid_triangle a b c) /\ ret = -1).

(* Example proof *)
Example triangle_area_example :
  problem_71_spec 3 4 5 6.0.
Proof.
  unfold problem_71_spec.
  left.
  split.
  - unfold is_valid_triangle. lra.
  - unfold is_rounded_to_2_decimals, heron_area.
    simpl.
    remember ((3 + 4 + 5) / 2) as s.
    assert (s = 6) by (subst s; reflexivity).
    rewrite H.
    simpl.
    assert (sqrt (6 * (6 - 3) * (6 - 4) * (6 - 5)) = 6.0).
    {
      simpl. unfold Rminus.
      replace (6 - 3) with 3 by lra.
      replace (6 - 4) with 2 by lra.
      replace (6 - 5) with 1 by lra.
      replace (6 * 3 * 2 * 1) with 36 by lra.
      rewrite sqrt_def; try lra.
      apply sqrt_positivity; lra.
    }
    rewrite H0.
    split.
    + exists 600%Z. reflexivity.
    + split; lra.
Qed.