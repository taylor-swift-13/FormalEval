Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 99 11.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 11 is prime *)
    apply prime_intro.
    + lia. (* 1 < 11 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 11 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10) by lia.
      destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 11 divides 99 *)
      exists 9. reflexivity.
    + (* Part 3: Prove that any prime factor k of 99 is <= 11 *)
      intros k Hk_prime Hk_div_99.
      assert (H_decomp: 99 = 9 * 11) by reflexivity.
      rewrite H_decomp in Hk_div_99.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_99; [| assumption].
      destruct Hk_div_99 as [Hk_div_9 | Hk_div_11].
      * (* Case k | 9 *)
        assert (H_decomp9: 9 = 3 * 3) by reflexivity.
        rewrite H_decomp9 in Hk_div_9.
        apply prime_mult in Hk_div_9; [| assumption].
        destruct Hk_div_9 as [Hk_div_3 | Hk_div_3].
        -- apply Z.divide_pos_le in Hk_div_3.
           ++ lia.
           ++ lia. (* 3 > 0 *)
        -- apply Z.divide_pos_le in Hk_div_3.
           ++ lia.
           ++ lia. (* 3 > 0 *)
      * (* Case k | 11 *)
        apply Z.divide_pos_le in Hk_div_11.
        -- lia.
        -- lia. (* 11 > 0 *)
Qed.