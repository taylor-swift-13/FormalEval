Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 10000 5.
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
    + exists 2000. reflexivity.
    + intros k Hk_prime Hk_div.
      assert (H_decomp: 10000 = 16 * 625) by reflexivity.
      rewrite H_decomp in Hk_div.
      apply prime_mult in Hk_div; [| assumption].
      destruct Hk_div as [H16 | H625].
      * replace 16 with (2 * 8) in H16 by reflexivity.
        apply prime_mult in H16; [| assumption].
        destruct H16 as [H2 | H8].
        { apply Z.divide_pos_le in H2; lia. }
        replace 8 with (2 * 4) in H8 by reflexivity.
        apply prime_mult in H8; [| assumption].
        destruct H8 as [H2 | H4].
        { apply Z.divide_pos_le in H2; lia. }
        replace 4 with (2 * 2) in H4 by reflexivity.
        apply prime_mult in H4; [| assumption].
        destruct H4 as [H2 | H2_2].
        { apply Z.divide_pos_le in H2; lia. }
        { apply Z.divide_pos_le in H2_2; lia. }
      * replace 625 with (5 * 125) in H625 by reflexivity.
        apply prime_mult in H625; [| assumption].
        destruct H625 as [H5 | H125].
        { apply Z.divide_pos_le in H5; lia. }
        replace 125 with (5 * 25) in H125 by reflexivity.
        apply prime_mult in H125; [| assumption].
        destruct H125 as [H5 | H25].
        { apply Z.divide_pos_le in H5; lia. }
        replace 25 with (5 * 5) in H25 by reflexivity.
        apply prime_mult in H25; [| assumption].
        destruct H25 as [H5 | H5_2].
        { apply Z.divide_pos_le in H5; lia. }
        { apply Z.divide_pos_le in H5_2; lia. }
Qed.