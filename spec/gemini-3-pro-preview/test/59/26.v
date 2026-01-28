Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 1763 43.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 43 is prime *)
    apply prime_intro.
    + lia. (* 1 < 43 *)
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/ n = 36 \/ n = 37 \/ n = 38 \/ n = 39 \/ n = 40 \/ n = 41 \/ n = 42) by lia.
      repeat match goal with
             | [ H : _ \/ _ |- _ ] => destruct H as [-> | H]
             end; subst; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 43 divides 1763 *)
      exists 41. reflexivity.
    + (* Part 3: Prove that any prime factor k of 1763 is <= 43 *)
      intros k Hk_prime Hk_div_1763.
      assert (H_decomp: 1763 = 41 * 43) by reflexivity.
      rewrite H_decomp in Hk_div_1763.
      apply prime_mult in Hk_div_1763; [| assumption].
      destruct Hk_div_1763 as [Hk_div_41 | Hk_div_43].
      * (* Case k | 41 *)
        apply Z.divide_pos_le in Hk_div_41.
        -- lia.
        -- lia. (* 41 > 0 *)
      * (* Case k | 43 *)
        apply Z.divide_pos_le in Hk_div_43.
        -- lia.
        -- lia. (* 43 > 0 *)
Qed.