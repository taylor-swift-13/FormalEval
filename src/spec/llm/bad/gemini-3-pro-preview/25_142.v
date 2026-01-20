Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma is_prime_Z_prime : forall n, is_prime n <-> Znumtheory.prime (Z.of_nat n).
Proof.
  intros n. split.
  - intros [H1 H2]. split.
    + apply Nat2Z.inj_lt. assumption.
    + intros m [Hm1 Hmn] Hdiv.
      apply Z2Nat.inj_divide in Hdiv; try lia.
      destruct (H2 (Z.to_nat m) Hdiv) as [Heq1 | Heq2].
      * apply (f_equal Z.of_nat) in Heq1. rewrite Z2Nat.id in Heq1; lia.
      * apply (f_equal Z.of_nat) in Heq2. rewrite Z2Nat.id in Heq2; lia.
  - intros [H1 H2]. split.
    + apply Nat2Z.inj_lt in H1. assumption.
    + intros d Hdiv.
      destruct (Nat.eq_dec d 1); auto.
      destruct (Nat.eq_dec d n); auto.
      exfalso.
      assert (1 < Z.of_nat d < Z.of_nat n).
      { split. 
        - apply Nat2Z.inj_lt. lia. 
        - apply Nat2Z.inj_lt. apply Nat.divide_pos_le in Hdiv; lia. 
      }
      apply (H2 (Z.of_nat d)); auto.
      apply Z.divide_of_nat_divide. assumption.
Qed.

Fixpoint check_divisors (n : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | 0%nat => true
  | S f =>
      if d * d >? n then true
      else if Z.eqb (n mod d) 0 then false
      else check_divisors n (d + 1) f
  end.

Definition is_prime_Z_efficient (n : Z) : bool :=
  if n <=? 1 then false
  else check_divisors n 2 (Z.to_nat (Z.sqrt n) + 2).

Lemma check_divisors_correct : forall n d fuel,
  2 <= d ->
  d * d <= n ->
  (Z.of_nat fuel) >= Z.sqrt n - d + 2 ->
  check_divisors n d fuel = true ->
  forall x, d <= x -> x * x <= n -> ~ (x | n).
Proof.
  intros n d fuel. revert d.
  induction fuel.
  - intros. simpl in H1. lia.
  - intros d Hd Hdd Hfuel Hcheck x Hdx Hxx Hdiv.
    simpl in Hcheck.
    destruct (d * d >? n) eqn:Hstop.
    + Z.gtb_spec d. lia.
    + destruct (n mod d =? 0) eqn:Hmod.
      * discriminate.
      * apply Z.eqb_neq in Hmod.
        assert (~ (d | n)). { intro. apply Z.mod_divide in H; auto; lia. }
        destruct (Z.eq_dec d x).
        -- subst. contradiction.
        -- apply (IHfuel (d + 1)); try lia.
           ++ destruct (Z.gtb_spec (d*d) n); try lia.
              assert (d < Z.sqrt n). 
              { apply Z.sqrt_lt_square; try lia. }
              lia.
           ++ assumption.
Qed.

Lemma is_prime_Z_efficient_correct : forall n,
  is_prime_Z_efficient n = true -> Znumtheory.prime n.
Proof.
  intros n Hcheck.
  unfold is_prime_Z_efficient in Hcheck.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Z.leb_nle in Hle.
    assert (Hn: n > 1) by lia.
    split; auto.
    intros m [Hm1 Hmn] Hdiv.
    destruct (Z.le_gt_dec (m * m) n).
    + eapply check_divisors_correct in Hcheck; try eassumption.
      * apply Hcheck in Hdiv. contradiction.
      * lia.
      * apply Z.sqrt_nonneg.
      * lia.
    + assert (Hdiv': (n/m | n)). { apply Z.divide_factor_r. assumption. }
      assert (Hnm: n/m * n/m <= n).
      {
         assert (Hmk: n = m * (n/m)). { apply Z.divide_div_mul_exact; auto; lia. }
         assert (Hk: n/m < m).
         { rewrite Hmk at 2. apply Z.mul_lt_mono_pos_r; try lia.
           assert (m * m > m * (n/m)). lia.
           rewrite <- Hmk. lia.
         }
         assert (n/m * n/m < m * (n/m)).
         { apply Z.mul_lt_mono_pos_r; try lia. 
           apply Z.div_str_pos; try lia. split; try lia. assumption. }
         rewrite <- Hmk in H. lia.
      }
      assert (Hnm_gt1: n/m >= 2).
      {
         assert (n/m > 1).
         { apply Z.div_str_pos; try lia. split; try lia. assumption. }
         lia.
      }
      eapply check_divisors_correct in Hcheck; try eassumption.
      * apply Hcheck in Hdiv'. contradiction.
      * lia.
      * apply Z.sqrt_nonneg.
      * lia.
Qed.

Example test_factorize_big : factorize_spec 9999999963 [3; 3; 3; 370370369]%nat.
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor.
      * apply is_prime_Z_prime. apply is_prime_Z_efficient_correct. vm_compute. reflexivity.
      * apply is_prime_Z_prime. apply is_prime_Z_efficient_correct. vm_compute. reflexivity.
      * apply is_prime_Z_prime. apply is_prime_Z_efficient_correct. vm_compute. reflexivity.
      * apply is_prime_Z_prime. apply is_prime_Z_efficient_correct. vm_compute. reflexivity.
    + repeat constructor; lia.
Qed.