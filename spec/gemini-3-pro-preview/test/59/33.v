Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 9996 17.
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
      repeat (destruct H_cases as [-> | H_cases]; [ compute; reflexivity | ]).
      subst; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 17 divides 9996 *)
      exists 588. reflexivity.
    + (* Part 3: Prove that any prime factor k of 9996 is <= 17 *)
      intros k Hk_prime Hk_div_9996.
      assert (H_decomp: 9996 = 17 * (7 * (7 * (3 * (2 * 2))))) by reflexivity.
      rewrite H_decomp in Hk_div_9996.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_9996; [| assumption].
      destruct Hk_div_9996 as [Hk_div_17 | Hk_rest].
      * (* Case k | 17 *)
        apply Z.divide_pos_le in Hk_div_17; [lia | lia].
      * (* Case k | (7 * ...) *)
        apply prime_mult in Hk_rest; [| assumption].
        destruct Hk_rest as [Hk_div_7a | Hk_rest].
        -- (* Case k | 7 *)
           apply Z.divide_pos_le in Hk_div_7a; [lia | lia].
        -- apply prime_mult in Hk_rest; [| assumption].
           destruct Hk_rest as [Hk_div_7b | Hk_rest].
           ++ (* Case k | 7 *)
              apply Z.divide_pos_le in Hk_div_7b; [lia | lia].
           ++ apply prime_mult in Hk_rest; [| assumption].
              destruct Hk_rest as [Hk_div_3 | Hk_rest].
              ** (* Case k | 3 *)
                 apply Z.divide_pos_le in Hk_div_3; [lia | lia].
              ** apply prime_mult in Hk_rest; [| assumption].
                 destruct Hk_rest as [Hk_div_2a | Hk_div_2b].
                 --- (* Case k | 2 *)
                     apply Z.divide_pos_le in Hk_div_2a; [lia | lia].
                 --- (* Case k | 2 *)
                     apply Z.divide_pos_le in Hk_div_2b; [lia | lia].
Qed.