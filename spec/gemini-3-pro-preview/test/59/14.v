Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 243 3.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - apply prime_intro.
    + lia.
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2) by lia.
      destruct H_cases as [-> | ->]; compute; reflexivity.
  - split.
    + exists 81. reflexivity.
    + intros k Hk_prime Hk_div.
      assert (H_decomp1: 243 = 3 * 81) by reflexivity.
      rewrite H_decomp1 in Hk_div.
      apply prime_mult in Hk_div; [| assumption].
      destruct Hk_div as [H | H].
      * apply Z.divide_pos_le in H; lia.
      * assert (H_decomp2: 81 = 3 * 27) by reflexivity.
        rewrite H_decomp2 in H.
        apply prime_mult in H; [| assumption].
        destruct H as [H | H].
        -- apply Z.divide_pos_le in H; lia.
        -- assert (H_decomp3: 27 = 3 * 9) by reflexivity.
           rewrite H_decomp3 in H.
           apply prime_mult in H; [| assumption].
           destruct H as [H | H].
           ++ apply Z.divide_pos_le in H; lia.
           ++ assert (H_decomp4: 9 = 3 * 3) by reflexivity.
              rewrite H_decomp4 in H.
              apply prime_mult in H; [| assumption].
              destruct H as [H | H]; apply Z.divide_pos_le in H; lia.
Qed.