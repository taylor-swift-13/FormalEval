Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Require Import Bool.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

(* Helper function to verify gcd(k, p) = 1 for all 1 <= k <= n *)
Fixpoint check_gcd (n : nat) (p : Z) : bool :=
  match n with
  | O => true
  | S k => (Z.gcd (Z.of_nat (S k)) p =? 1) && check_gcd k p
  end.

Lemma check_gcd_ok : forall n p, check_gcd n p = true -> 
  forall k, 1 <= k <= Z.of_nat n -> Z.gcd k p = 1.
Proof.
  induction n; intros p Hcheck k Hk.
  - simpl in Hk. lia.
  - simpl in Hcheck. apply andb_true_iff in Hcheck. destruct Hcheck as [Hcurr Hrec].
    assert (k = Z.of_nat (S n) \/ k < Z.of_nat (S n)) by lia.
    destruct H as [->|Hlt].
    + apply Z.eqb_eq in Hcurr. assumption.
    + apply IHn; try assumption. lia.
Qed.

Example test_case : largest_prime_factor_spec 1765 353.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Part 1: Prove that 353 is prime *)
    apply prime_intro.
    + lia. (* 1 < 353 *)
    + intros n Hn.
      (* Check relative primality for 1 <= n < 353 using computation *)
      apply Zgcd_1_rel_prime.
      apply (check_gcd_ok 352 353).
      * vm_compute. reflexivity.
      * lia.
  - split.
    + (* Part 2: Prove that 353 divides 1765 *)
      exists 5. reflexivity.
    + (* Part 3: Prove that any prime factor k of 1765 is <= 353 *)
      intros k Hk_prime Hk_div_1765.
      assert (H_decomp: 1765 = 5 * 353) by reflexivity.
      rewrite H_decomp in Hk_div_1765.
      (* Use the property that if a prime divides a product, it divides one of the factors *)
      apply prime_mult in Hk_div_1765; [| assumption].
      destruct Hk_div_1765 as [Hk_div_5 | Hk_div_353].
      * (* Case k | 5 *)
        apply Z.divide_pos_le in Hk_div_5.
        -- lia.
        -- lia. (* 5 > 0 *)
      * (* Case k | 353 *)
        apply Z.divide_pos_le in Hk_div_353.
        -- lia.
        -- lia. (* 353 > 0 *)
Qed.