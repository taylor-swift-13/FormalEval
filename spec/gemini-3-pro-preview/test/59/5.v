Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 13195 29.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 29 is prime *)
    apply prime_intro.
    + lia. (* 1 < 29 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 29 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ 
                      n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ 
                      n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ 
                      n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28) by lia.
      repeat destruct H_cases as [-> | H_cases]; try (compute; reflexivity).
      subst; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 29 divides 13195 *)
      exists 455. reflexivity.
    + (* Part 3: Prove that any prime factor k of 13195 is <= 29 *)
      intros k Hk_prime Hk_div_13195.
      assert (H_decomp: 13195 = 5 * (7 * (13 * 29))) by reflexivity.
      rewrite H_decomp in Hk_div_13195.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_13195; [| assumption].
      destruct Hk_div_13195 as [Hk_div_5 | H_rest1].
      * (* Case k | 5 *)
        apply Z.divide_pos_le in Hk_div_5; lia.
      * (* Case k | 7 * 13 * 29 *)
        apply prime_mult in H_rest1; [| assumption].
        destruct H_rest1 as [Hk_div_7 | H_rest2].
        -- (* Case k | 7 *)
           apply Z.divide_pos_le in Hk_div_7; lia.
        -- (* Case k | 13 * 29 *)
           apply prime_mult in H_rest2; [| assumption].
           destruct H_rest2 as [Hk_div_13 | Hk_div_29].
           ++ (* Case k | 13 *)
              apply Z.divide_pos_le in Hk_div_13; lia.
           ++ (* Case k | 29 *)
              apply Z.divide_pos_le in Hk_div_29; lia.
Qed.