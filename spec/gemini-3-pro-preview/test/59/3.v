Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 63 7.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 7 is prime *)
    apply prime_intro.
    + lia. (* 1 < 7 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 7 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6) by lia.
      destruct H_cases as [-> | [-> | [-> | [-> | [-> | ->]]]]]; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 7 divides 63 *)
      exists 9. reflexivity.
    + (* Part 3: Prove that any prime factor k of 63 is <= 7 *)
      intros k Hk_prime Hk_div_63.
      assert (H_decomp: 63 = 7 * 9) by reflexivity.
      rewrite H_decomp in Hk_div_63.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_63; [| assumption].
      destruct Hk_div_63 as [Hk_div_7 | Hk_div_9].
      * (* Case k | 7 *)
        apply Z.divide_pos_le in Hk_div_7.
        -- lia.
        -- lia. (* 7 > 0 *)
      * (* Case k | 9 *)
        assert (H_decomp9: 9 = 3 * 3) by reflexivity.
        rewrite H_decomp9 in Hk_div_9.
        apply prime_mult in Hk_div_9; [| assumption].
        destruct Hk_div_9 as [Hk_div_3 | Hk_div_3];
        apply Z.divide_pos_le in Hk_div_3; try lia.
Qed.