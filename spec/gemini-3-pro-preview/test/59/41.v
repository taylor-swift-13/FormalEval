Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 1023 31.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - apply prime_intro.
    + lia.
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      assert (H_cases : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30) by lia.
      repeat (destruct H_cases as [-> | H_cases]; [ compute; reflexivity | ]).
      subst; compute; reflexivity.
  - split.
    + exists 33. reflexivity.
    + intros k Hk_prime Hk_div.
      assert (H_decomp: 1023 = 3 * 11 * 31) by reflexivity.
      rewrite H_decomp in Hk_div.
      apply prime_mult in Hk_div; [| assumption].
      destruct Hk_div as [H_3_11 | H_31].
      * apply prime_mult in H_3_11; [| assumption].
        destruct H_3_11 as [H_3 | H_11].
        -- apply Z.divide_pos_le in H_3.
           ++ lia.
           ++ lia.
        -- apply Z.divide_pos_le in H_11.
           ++ lia.
           ++ lia.
      * apply Z.divide_pos_le in H_31.
        -- lia.
        -- lia.
Qed.