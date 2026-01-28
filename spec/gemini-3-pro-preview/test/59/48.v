Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 117 13.
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
    + (* Part 2: Prove that 13 divides 117 *)
      exists 9. reflexivity.
    + (* Part 3: Prove that any prime factor k of 117 is <= 13 *)
      intros k Hk_prime Hk_div_117.
      assert (H_decomp: 117 = 9 * 13) by reflexivity.
      rewrite H_decomp in Hk_div_117.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_117; [| assumption].
      destruct Hk_div_117 as [Hk_div_9 | Hk_div_13].
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
      * (* Case k | 13 *)
        apply Z.divide_pos_le in Hk_div_13.
        -- lia.
        -- lia. (* 13 > 0 *)
Qed.