Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 252 7.
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
    + (* Part 2: Prove that 7 divides 252 *)
      exists 36. reflexivity.
    + (* Part 3: Prove that any prime factor k of 252 is <= 7 *)
      intros k Hk_prime Hk_div_252.
      assert (H_decomp: 252 = 2 * (2 * (3 * (3 * 7)))) by reflexivity.
      rewrite H_decomp in Hk_div_252.
      (* Repeatedly apply prime_mult *)
      apply prime_mult in Hk_div_252; [| assumption].
      destruct Hk_div_252 as [Hk_div_2 | Hk_rest1].
      * apply Z.divide_pos_le in Hk_div_2; lia.
      * apply prime_mult in Hk_rest1; [| assumption].
        destruct Hk_rest1 as [Hk_div_2_2 | Hk_rest2].
        -- apply Z.divide_pos_le in Hk_div_2_2; lia.
        -- apply prime_mult in Hk_rest2; [| assumption].
           destruct Hk_rest2 as [Hk_div_3 | Hk_rest3].
           ++ apply Z.divide_pos_le in Hk_div_3; lia.
           ++ apply prime_mult in Hk_rest3; [| assumption].
              destruct Hk_rest3 as [Hk_div_3_2 | Hk_div_7].
              ** apply Z.divide_pos_le in Hk_div_3_2; lia.
              ** apply Z.divide_pos_le in Hk_div_7; lia.
Qed.