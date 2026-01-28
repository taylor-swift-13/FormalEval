Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 4096 2.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - apply prime_2.
  - split.
    + exists 2048. reflexivity.
    + intros k Hk_prime Hk_div.
      assert (H64: (k | 64)).
      { replace 4096 with (64 * 64) in Hk_div by reflexivity.
        apply prime_mult in Hk_div; [| assumption].
        destruct Hk_div; assumption. }
      assert (H8: (k | 8)).
      { replace 64 with (8 * 8) in H64 by reflexivity.
        apply prime_mult in H64; [| assumption].
        destruct H64; assumption. }
      replace 8 with (2 * 4) in H8 by reflexivity.
      apply prime_mult in H8; [| assumption].
      destruct H8 as [H2 | H4].
      * apply Z.divide_pos_le in H2; lia.
      * replace 4 with (2 * 2) in H4 by reflexivity.
        apply prime_mult in H4; [| assumption].
        destruct H4 as [H2 | H2]; apply Z.divide_pos_le in H2; lia.
Qed.