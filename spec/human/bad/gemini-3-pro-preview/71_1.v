Require Import Reals.
Require Import ZArith.
Require Import Psatz.
Open Scope R_scope.

(* Definitions provided in the specification *)

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

(* Example Proof *)

Example test_triangle_area_3_4_5 : problem_71_spec 3 4 5 6.
Proof.
  unfold problem_71_spec.
  left.
  split.
  - (* Prove is_valid_triangle 3 4 5 *)
    unfold is_valid_triangle.
    lra.
  - (* Prove is_rounded_to_2_decimals 6 (heron_area 3 4 5) *)
    unfold heron_area.
    (* Step 1: Simplify the arithmetic inside the square root *)
    replace ((3 + 4 + 5) / 2) with 6 by lra.
    replace (6 * (6 - 3) * (6 - 4) * (6 - 5)) with (Rsqr 6).
    2: { unfold Rsqr; lra. }
    
    (* Step 2: Resolve the square root using sqrt_Rsqr *)
    (* sqrt_Rsqr: forall x, 0 <= x -> sqrt (Rsqr x) = x *)
    rewrite sqrt_Rsqr.
    + (* Prove rounding properties *)
      unfold is_rounded_to_2_decimals.
      split.
      * (* Existence of integer z *)
        exists 600%Z.
        unfold IZR.
        lra.
      * (* Bounds check *)
        lra.
    + (* Proof precondition for sqrt_Rsqr: 0 <= 6 *)
      lra.
Qed.