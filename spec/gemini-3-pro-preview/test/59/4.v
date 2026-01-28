Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 330 11.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - apply prime_intro.
    + lia.
    + intros n Hn.
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10) by lia.
      destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; compute; reflexivity.
  - split.
    + exists 30. reflexivity.
    + intros k Hk_prime Hk_div.
      assert (H_decomp: 330 = 11 * (5 * (3 * 2))) by reflexivity.
      rewrite H_decomp in Hk_div.
      apply prime_mult in Hk_div; [| assumption].
      destruct Hk_div as [Hk | Hk].
      * apply Z.divide_pos_le in Hk; [lia | lia].
      * apply prime_mult in Hk; [| assumption].
        destruct Hk as [Hk | Hk].
        -- apply Z.divide_pos_le in Hk; [lia | lia].
        -- apply prime_mult in Hk; [| assumption].
           destruct Hk as [Hk | Hk].
           ++ apply Z.divide_pos_le in Hk; [lia | lia].
           ++ apply Z.divide_pos_le in Hk; [lia | lia].
Qed.