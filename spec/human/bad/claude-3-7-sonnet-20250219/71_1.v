Require Import Reals.
Require Import ZArith.
Open Scope R_scope.
Open Scope Z_scope.

Definition is_valid_triangle (a b c : R) : Prop :=
  a > 0 /\ b > 0 /\ c > 0 /\
  a + b > c /\ a + c > b /\ b + c > a.

Definition heron_area (a b c : R) : R :=
  let s := (a + b + c) / 2 in
  sqrt (s * (s - a) * (s - b) * (s - c)).

Definition is_rounded_to_2_decimals (rounded_val original_val : R) : Prop :=
  (exists z : Z, rounded_val = IZR z / 100) /\
  rounded_val - /200 <= original_val /\ original_val < rounded_val + /200.

Definition problem_71_spec (a b c : R) (ret : R) : Prop :=
  (is_valid_triangle a b c /\ is_rounded_to_2_decimals ret (heron_area a b c))
  \/
  (~ (is_valid_triangle a b c) /\ ret = -1).

(* Helper lemma for sqrt of 36 *)
Lemma sqrt_36 : sqrt 36 = 6.
Proof.
  apply sqrt_unique.
  - lra.
  - rewrite Rmult_comm.
    replace (6 * 6) with 36 by lra.
    reflexivity.
Qed.

(* The test case uses integer inputs 3,4,5 but the spec expects R.
   So convert inputs from Z to R using IZR.
   Show that problem_71_spec (IZR 3) (IZR 4) (IZR 5) 6 holds.
*)
Example test_case_3_4_5 :
  problem_71_spec (IZR 3) (IZR 4) (IZR 5) 6.
Proof.
  unfold problem_71_spec.
  left.
  split.
  - unfold is_valid_triangle.
    split; [lra|].
    split; [lra|].
    split; [lra|].
    split; [lra|].
    split; [lra| lra].
  - unfold is_rounded_to_2_decimals.
    split.
    + exists 600%Z.
      simpl.
      reflexivity.
    + split.
      * unfold heron_area.
        simpl.
        replace ((IZR 3 + IZR 4 + IZR 5) / 2) with 6 by lra.
        replace (6 * (6 - IZR 3) * (6 - IZR 4) * (6 - IZR 5)) with 36 by (repeat rewrite Rmult_assoc; lra).
        rewrite sqrt_36.
        lra.
      * unfold heron_area.
        simpl.
        replace ((IZR 3 + IZR 4 + IZR 5) / 2) with 6 by lra.
        replace (6 * (6 - IZR 3) * (6 - IZR 4) * (6 - IZR 5)) with 36 by (repeat rewrite Rmult_assoc; lra).
        rewrite sqrt_36.
        lra.
Qed.