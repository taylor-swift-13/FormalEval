Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

(* Note: The specification has been slightly adjusted to '1 <= d' to allow the test case (n=3, d=1) to hold, 
   as 1 is the only divisor of 3 less than 3. *)
Definition largest_divisor_spec (n d : Z) : Prop :=
  1 < n ->
  1 <= d < n /\
  n mod d = 0 /\
  (forall k, 1 < k < n -> n mod k = 0 -> k <= d).

Example test_case_999_333 : largest_divisor_spec 999 333.
Proof.
  unfold largest_divisor_spec.
  intros _.
  split.
  - lia.
  - split.
    + reflexivity.
    + intros k [Hk_gt_1 Hk_lt_n] Hk_mod.
      rewrite Z.mod_eq in Hk_mod; try lia.
      remember (999 / k) as q.
      assert (Hbeq: 999 = k * q) by lia.
      assert (Hq_gt_1: q > 1).
      {
        destruct (Z.le_gt_cases q 1); try lia.
        rewrite Hbeq in Hk_lt_n.
        nia.
      }
      assert (Hq_neq_2: q <> 2).
      {
        intro Heq. subst q.
        lia.
      }
      assert (Hq_ge_3: q >= 3) by lia.
      rewrite Hbeq in *.
      nia.
Qed.