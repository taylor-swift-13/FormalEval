Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 874 23.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 23 is prime *)
    apply prime_intro.
    + lia.
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22) by lia.
      repeat (destruct H_cases as [-> | H_cases]; [ compute; reflexivity | ]).
      subst; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 23 divides 874 *)
      exists 38. reflexivity.
    + (* Part 3: Prove that any prime factor k of 874 is <= 23 *)
      intros k Hk_prime Hk_div_874.
      assert (H_decomp: 874 = 23 * 38) by reflexivity.
      rewrite H_decomp in Hk_div_874.
      apply prime_mult in Hk_div_874; [| assumption].
      destruct Hk_div_874 as [Hk_div_23 | Hk_div_38].
      * apply Z.divide_pos_le in Hk_div_23; lia.
      * assert (H_decomp38: 38 = 2 * 19) by reflexivity.
        rewrite H_decomp38 in Hk_div_38.
        apply prime_mult in Hk_div_38; [| assumption].
        destruct Hk_div_38 as [Hk_div_2 | Hk_div_19].
        -- apply Z.divide_pos_le in Hk_div_2; lia.
        -- apply Z.divide_pos_le in Hk_div_19; lia.
Qed.