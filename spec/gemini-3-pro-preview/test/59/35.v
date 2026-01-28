Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 253 23.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove 23 is prime *)
    apply prime_intro.
    + lia. (* 1 < 23 *)
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      (* Check relative primality for 1 <= n < 23 *)
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
              n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
              n = 21 \/ n = 22) by lia.
      repeat (destruct H_cases as [-> | H_cases]; [ compute; reflexivity | ]).
      subst; compute; reflexivity.
  - split.
    + (* Part 2: Prove 23 divides 253 *)
      exists 11. reflexivity.
    + (* Part 3: Prove that any prime factor k of 253 is <= 23 *)
      intros k Hk_prime Hk_div_253.
      assert (H_decomp: 253 = 11 * 23) by reflexivity.
      rewrite H_decomp in Hk_div_253.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_253; [| assumption].
      destruct Hk_div_253 as [Hk_div_11 | Hk_div_23].
      * (* Case k | 11 *)
        apply Z.divide_pos_le in Hk_div_11.
        -- lia.
        -- lia. (* 11 > 0 *)
      * (* Case k | 23 *)
        apply Z.divide_pos_le in Hk_div_23.
        -- lia.
        -- lia. (* 23 > 0 *)
Qed.