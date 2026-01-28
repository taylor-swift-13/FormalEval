Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 500 5.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 5 is prime *)
    apply prime_intro.
    + lia. (* 1 < 5 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 5 *)
      apply Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
      destruct H_cases as [-> | [-> | [-> | ->]]]; compute; reflexivity.
  - split.
    + (* Part 2: Prove that 5 divides 500 *)
      exists 100. reflexivity.
    + (* Part 3: Prove that any prime factor k of 500 is <= 5 *)
      intros k Hk_prime Hk_div.
      assert (H_decomp: 500 = 2 * 2 * 5 * 5 * 5) by reflexivity.
      rewrite H_decomp in Hk_div.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      repeat (apply prime_mult in Hk_div; [destruct Hk_div as [Hk_div | Hk_div] | assumption]).
      (* Handle all resulting cases: k | 2 or k | 5 *)
      all: apply Z.divide_pos_le in Hk_div; [ lia | lia ].
Qed.