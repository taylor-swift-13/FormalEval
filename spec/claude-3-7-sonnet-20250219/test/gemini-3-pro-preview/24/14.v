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

Example test_case_72_36 : largest_divisor_spec 72 36.
Proof.
  unfold largest_divisor_spec.
  intros Hn.
  split.
  - lia.
  - split.
    + reflexivity.
    + intros k Hk_range Hk_mod.
      apply Z.mod_divide in Hk_mod; [|lia].
      destruct Hk_mod as [z Hz].
      assert (Hz_ge_2 : z >= 2).
      {
        destruct (Z_le_gt_dec z 1).
        - assert (z * k <= 1 * k) by (apply Z.mul_le_mono_nonneg_r; lia).
          lia.
        - lia.
      }
      assert (2 * k <= z * k) by (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
Qed.