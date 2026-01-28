Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 873 97.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove 97 is prime *)
    destruct (prime_dec 97) as [H_prime | H_not_prime].
    + exact H_prime.
    + exfalso.
      apply prime_divisors in H_not_prime; [| lia].
      destruct H_not_prime as [d [Hd_prime [Hd_div Hd_sq]]].
      (* d is prime, d | 97, d^2 <= 97 implies d <= 9 *)
      assert (Hd_bound: d <= 9).
      {
        destruct (Z_lt_dec d 10); [lia|].
        assert (d >= 10) by lia.
        assert (d * d >= 100).
        { apply Z.mul_le_mono_nonneg; lia. }
        lia.
      }
      (* Primes <= 9 are 2, 3, 5, 7 *)
      assert (d = 2 \/ d = 3 \/ d = 5 \/ d = 7).
      {
        destruct Hd_prime as [H1 H2].
        assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
        destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
        - left; reflexivity. (* 2 *)
        - right; left; reflexivity. (* 3 *)
        - (* 4 *) exfalso; specialize (H2 2); assert (1 <= 2 < 4) by lia; apply H2 in H; compute in H; discriminate.
        - right; right; left; reflexivity. (* 5 *)
        - (* 6 *) exfalso; specialize (H2 2); assert (1 <= 2 < 6) by lia; apply H2 in H; compute in H; discriminate.
        - right; right; right; reflexivity. (* 7 *)
        - (* 8 *) exfalso; specialize (H2 2); assert (1 <= 2 < 8) by lia; apply H2 in H; compute in H; discriminate.
        - (* 9 *) exfalso; specialize (H2 3); assert (1 <= 3 < 9) by lia; apply H2 in H; compute in H; discriminate.
      }
      destruct H as [-> | [-> | [-> | ->]]];
      apply Z.mod_divide in Hd_div; try lia;
      compute in Hd_div; discriminate.
  - split.
    + (* Part 2: Prove 97 divides 873 *)
      exists 9. reflexivity.
    + (* Part 3: Prove any prime factor k of 873 is <= 97 *)
      intros k Hk_prime Hk_div.
      assert (H_decomp: 873 = 9 * 97) by reflexivity.
      rewrite H_decomp in Hk_div.
      apply prime_mult in Hk_div; [| exact Hk_prime].
      destruct Hk_div as [Hk_div_9 | Hk_div_97].
      * (* Case k | 9 *)
        assert (H_9: 9 = 3 * 3) by reflexivity.
        rewrite H_9 in Hk_div_9.
        apply prime_mult in Hk_div_9; [| exact Hk_prime].
        destruct Hk_div_9 as [Hk_div_3 | Hk_div_3].
        -- apply Z.divide_pos_le in Hk_div_3; [| lia].
           lia.
        -- apply Z.divide_pos_le in Hk_div_3; [| lia].
           lia.
      * (* Case k | 97 *)
        apply Z.divide_pos_le in Hk_div_97; [| lia].
        lia.
Qed.