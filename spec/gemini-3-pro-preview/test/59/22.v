Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 255 17.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 17 is prime *)
    apply prime_intro.
    + lia. (* 1 < 17 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 17 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
      destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 17 divides 255 *)
      exists 15. reflexivity.
    + (* Part 3: Prove that any prime factor k of 255 is <= 17 *)
      intros k Hk_prime Hk_div_255.
      assert (H_decomp: 255 = 3 * (5 * 17)) by reflexivity.
      rewrite H_decomp in Hk_div_255.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_255; [| assumption].
      destruct Hk_div_255 as [Hk_div_3 | Hk_div_rest].
      * (* Case k | 3 *)
        apply Z.divide_pos_le in Hk_div_3.
        -- lia.
        -- lia. (* 3 > 0 *)
      * (* Case k | 5 * 17 *)
        apply prime_mult in Hk_div_rest; [| assumption].
        destruct Hk_div_rest as [Hk_div_5 | Hk_div_17].
        -- (* Case k | 5 *)
           apply Z.divide_pos_le in Hk_div_5.
           ++ lia.
           ++ lia. (* 5 > 0 *)
        -- (* Case k | 17 *)
           apply Z.divide_pos_le in Hk_div_17.
           ++ lia.
           ++ lia. (* 17 > 0 *)
Qed.