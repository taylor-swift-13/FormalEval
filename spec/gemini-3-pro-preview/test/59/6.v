Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 100 5.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - apply prime_intro.
    + lia.
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
      destruct H_cases as [-> | [-> | [-> | ->]]]; compute; reflexivity.
  - split.
    + exists 20. reflexivity.
    + intros k Hk_prime Hk_div_100.
      assert (H_decomp: 100 = 4 * 25) by reflexivity.
      rewrite H_decomp in Hk_div_100.
      apply prime_mult in Hk_div_100; [| assumption].
      destruct Hk_div_100 as [Hk_div_4 | Hk_div_25].
      * assert (H4: 4 = 2 * 2) by reflexivity.
        rewrite H4 in Hk_div_4.
        apply prime_mult in Hk_div_4; [| assumption].
        destruct Hk_div_4 as [Hk_div_2 | Hk_div_2];
          apply Z.divide_pos_le in Hk_div_2; lia.
      * assert (H25: 25 = 5 * 5) by reflexivity.
        rewrite H25 in Hk_div_25.
        apply prime_mult in Hk_div_25; [| assumption].
        destruct Hk_div_25 as [Hk_div_5 | Hk_div_5];
          apply Z.divide_pos_le in Hk_div_5; lia.
Qed.