Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 4095 13.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 13 is prime *)
    apply prime_intro.
    + lia. (* 1 < 13 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 13 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12) by lia.
      destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 13 divides 4095 *)
      exists 315. reflexivity.
    + (* Part 3: Prove that any prime factor k of 4095 is <= 13 *)
      intros k Hk_prime Hk_div_4095.
      assert (H_decomp: 4095 = 3 * 3 * 5 * 7 * 13) by reflexivity.
      rewrite H_decomp in Hk_div_4095.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      (* The product associates as (((3 * 3) * 5) * 7) * 13 *)
      apply prime_mult in Hk_div_4095; [| assumption].
      destruct Hk_div_4095 as [H_rest1 | H_div_13].
      * (* Case k | 3 * 3 * 5 * 7 *)
        apply prime_mult in H_rest1; [| assumption].
        destruct H_rest1 as [H_rest2 | H_div_7].
        -- (* Case k | 3 * 3 * 5 *)
           apply prime_mult in H_rest2; [| assumption].
           destruct H_rest2 as [H_rest3 | H_div_5].
           ++ (* Case k | 3 * 3 *)
              apply prime_mult in H_rest3; [| assumption].
              destruct H_rest3 as [H_div_3a | H_div_3b].
              ** apply Z.divide_pos_le in H_div_3a; lia.
              ** apply Z.divide_pos_le in H_div_3b; lia.
           ++ (* Case k | 5 *)
              apply Z.divide_pos_le in H_div_5; lia.
        -- (* Case k | 7 *)
           apply Z.divide_pos_le in H_div_7; lia.
      * (* Case k | 13 *)
        apply Z.divide_pos_le in H_div_13; lia.
Qed.