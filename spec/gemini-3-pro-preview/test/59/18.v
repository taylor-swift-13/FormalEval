Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 120 5.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 5 is prime *)
    apply prime_intro.
    + lia. (* 1 < 5 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 5 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
      destruct H_cases as [-> | [-> | [-> | ->]]]; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 5 divides 120 *)
      exists 24. reflexivity.
    + (* Part 3: Prove that any prime factor k of 120 is <= 5 *)
      intros k Hk_prime Hk_div_120.
      assert (H_decomp: 120 = 5 * 24) by reflexivity.
      rewrite H_decomp in Hk_div_120.
      apply prime_mult in Hk_div_120; [| assumption].
      destruct Hk_div_120 as [Hk_div_5 | Hk_div_24].
      * (* Case k | 5 *)
        apply Z.divide_pos_le in Hk_div_5.
        -- lia.
        -- lia. (* 5 > 0 *)
      * (* Case k | 24 *)
        assert (H_decomp24: 24 = 3 * 8) by reflexivity.
        rewrite H_decomp24 in Hk_div_24.
        apply prime_mult in Hk_div_24; [| assumption].
        destruct Hk_div_24 as [Hk_div_3 | Hk_div_8].
        -- (* Case k | 3 *)
           apply Z.divide_pos_le in Hk_div_3.
           ++ lia.
           ++ lia. (* 3 > 0 *)
        -- (* Case k | 8 *)
           assert (H_decomp8: 8 = 2 * 4) by reflexivity.
           rewrite H_decomp8 in Hk_div_8.
           apply prime_mult in Hk_div_8; [| assumption].
           destruct Hk_div_8 as [Hk_div_2 | Hk_div_4].
           ++ (* Case k | 2 *)
              apply Z.divide_pos_le in Hk_div_2.
              ** lia.
              ** lia. (* 2 > 0 *)
           ++ (* Case k | 4 *)
              assert (H_decomp4: 4 = 2 * 2) by reflexivity.
              rewrite H_decomp4 in Hk_div_4.
              apply prime_mult in Hk_div_4; [| assumption].
              destruct Hk_div_4 as [Hk_div_2_a | Hk_div_2_b];
              apply Z.divide_pos_le in Hk_div_2_a || apply Z.divide_pos_le in Hk_div_2_b; try lia.
Qed.