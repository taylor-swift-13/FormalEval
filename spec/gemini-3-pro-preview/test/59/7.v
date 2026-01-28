Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 256 2.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 2 is prime *)
    apply prime_2.
  - split.
    + (* Part 2: Prove that 2 divides 256 *)
      exists 128. reflexivity.
    + (* Part 3: Prove that any prime factor k of 256 is <= 2 *)
      intros k Hk_prime Hk_div_256.
      (* Decompose 256 repeatedly to show that k must divide 2 *)
      assert (H_decomp1: 256 = 2 * 128) by reflexivity.
      rewrite H_decomp1 in Hk_div_256.
      apply prime_mult in Hk_div_256; [| assumption].
      destruct Hk_div_256 as [Hk_div_2 | Hk_div_128].
      * apply Z.divide_pos_le in Hk_div_2; lia.
      * assert (H_decomp2: 128 = 2 * 64) by reflexivity.
        rewrite H_decomp2 in Hk_div_128.
        apply prime_mult in Hk_div_128; [| assumption].
        destruct Hk_div_128 as [Hk_div_2 | Hk_div_64].
        -- apply Z.divide_pos_le in Hk_div_2; lia.
        -- assert (H_decomp3: 64 = 2 * 32) by reflexivity.
           rewrite H_decomp3 in Hk_div_64.
           apply prime_mult in Hk_div_64; [| assumption].
           destruct Hk_div_64 as [Hk_div_2 | Hk_div_32].
           ++ apply Z.divide_pos_le in Hk_div_2; lia.
           ++ assert (H_decomp4: 32 = 2 * 16) by reflexivity.
              rewrite H_decomp4 in Hk_div_32.
              apply prime_mult in Hk_div_32; [| assumption].
              destruct Hk_div_32 as [Hk_div_2 | Hk_div_16].
              ** apply Z.divide_pos_le in Hk_div_2; lia.
              ** assert (H_decomp5: 16 = 2 * 8) by reflexivity.
                 rewrite H_decomp5 in Hk_div_16.
                 apply prime_mult in Hk_div_16; [| assumption].
                 destruct Hk_div_16 as [Hk_div_2 | Hk_div_8].
                 --- apply Z.divide_pos_le in Hk_div_2; lia.
                 --- assert (H_decomp6: 8 = 2 * 4) by reflexivity.
                     rewrite H_decomp6 in Hk_div_8.
                     apply prime_mult in Hk_div_8; [| assumption].
                     destruct Hk_div_8 as [Hk_div_2 | Hk_div_4].
                     +++ apply Z.divide_pos_le in Hk_div_2; lia.
                     +++ assert (H_decomp7: 4 = 2 * 2) by reflexivity.
                         rewrite H_decomp7 in Hk_div_4.
                         apply prime_mult in Hk_div_4; [| assumption].
                         destruct Hk_div_4 as [Hk_div_2 | Hk_div_2_final].
                         *** apply Z.divide_pos_le in Hk_div_2; lia.
                         *** apply Z.divide_pos_le in Hk_div_2_final; lia.
Qed.