Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 1764 7.
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
    + (* Part 2: Prove that 7 divides 1764 *)
      exists 252. reflexivity.
    + (* Part 3: Prove that any prime factor k of 1764 is <= 7 *)
      intros k Hk_prime Hk_div_1764.
      assert (H_decomp: 1764 = 36 * 49) by reflexivity.
      rewrite H_decomp in Hk_div_1764.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_1764; [| assumption].
      destruct Hk_div_1764 as [Hk_div_36 | Hk_div_49].
      * (* Case k | 36 *)
        assert (H_decomp36: 36 = 4 * 9) by reflexivity.
        rewrite H_decomp36 in Hk_div_36.
        apply prime_mult in Hk_div_36; [| assumption].
        destruct Hk_div_36 as [Hk_div_4 | Hk_div_9].
        -- (* k | 4 *)
           assert (H_decomp4: 4 = 2 * 2) by reflexivity.
           rewrite H_decomp4 in Hk_div_4.
           apply prime_mult in Hk_div_4; [| assumption].
           destruct Hk_div_4 as [Hk_div_2 | Hk_div_2];
           apply Z.divide_pos_le in Hk_div_2; lia.
        -- (* k | 9 *)
           assert (H_decomp9: 9 = 3 * 3) by reflexivity.
           rewrite H_decomp9 in Hk_div_9.
           apply prime_mult in Hk_div_9; [| assumption].
           destruct Hk_div_9 as [Hk_div_3 | Hk_div_3];
           apply Z.divide_pos_le in Hk_div_3; lia.
      * (* Case k | 49 *)
        assert (H_decomp49: 49 = 7 * 7) by reflexivity.
        rewrite H_decomp49 in Hk_div_49.
        apply prime_mult in Hk_div_49; [| assumption].
        destruct Hk_div_49 as [Hk_div_7 | Hk_div_7];
        apply Z.divide_pos_le in Hk_div_7; lia.
Qed.