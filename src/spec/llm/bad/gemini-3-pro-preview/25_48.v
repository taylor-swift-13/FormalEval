Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helpers for primality checking using Z to avoid performance issues with large nats *)
Section ZPrimality.
  Open Scope Z_scope.

  Lemma nat_divide_to_Z_divide : forall a b : nat,
    Nat.divide a b -> (Z.of_nat a | Z.of_nat b).
  Proof.
    intros a b [k Hk]. exists (Z.of_nat k).
    rewrite <- Nat2Z.inj_mul. rewrite Hk. reflexivity.
  Qed.

  Lemma Z_prime_to_nat_prime : forall p : Z,
    (0 <= p) -> prime p -> is_prime (Z.to_nat p).
  Proof.
    intros p Hp Hprime.
    apply prime_alt in Hprime. destruct Hprime as [H1 Hdiv].
    split.
    - apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia.
    - intros d Hd.
      apply nat_divide_to_Z_divide in Hd.
      rewrite Z2Nat.id in Hd; try lia.
      destruct (Z_le_gt_dec (Z.of_nat d) 1) as [Hle|Hgt].
      + left. apply Nat2Z.inj. destruct (Z.of_nat d) eqn:Heq; try lia.
        * destruct Hd as [z Hz].
          assert (p = 0). { rewrite Hz. ring. }
          lia.
        * reflexivity.
      + right. apply Nat2Z.inj. rewrite Z2Nat.id; try lia.
        destruct (Z_lt_ge_dec (Z.of_nat d) p) as [Hlt|Hge].
        * exfalso. apply (Hdiv (Z.of_nat d)); try lia.
        * destruct Hd as [k Hk].
          assert (k = 1).
          {
            assert (p * 1 <= p * k). { rewrite <- Hk. lia. }
            apply Z.mul_le_mono_pos_l in H; try lia.
          }
          subst. rewrite Z.mul_1_r in Hk. symmetry. apply Hk.
  Qed.

  (* A computational primality test for Z *)
  Fixpoint check_divisors (d : Z) (fuel : nat) (p : Z) : bool :=
    match fuel with
    | O => false
    | S f => 
      if (d * d >? p) then true
      else if (p mod d =? 0) then false
      else check_divisors (d + 1) f p
    end.

  Definition check_prime (p : Z) : bool :=
    if (p <=? 1) then false
    else check_divisors 2 (Z.to_nat (Z.sqrt p) + 2) p.

  Lemma check_divisors_sound : forall fuel d p,
    0 <= p -> 2 <= d ->
    check_divisors d fuel p = true ->
    (forall k, d <= k -> k * k <= p -> ~ (k | p)).
  Proof.
    induction fuel; intros d p Hp Hd Hchk k Hdk Hkp Hdiv.
    - discriminate.
    - simpl in Hchk.
      destruct (d * d >? p) eqn:Hsq.
      + apply Z.gt_lt in Hsq. lia.
      + destruct (p mod d =? 0) eqn:Hrem.
        * discriminate.
        * apply Z.eqb_neq in Hrem.
          assert (~ (d | p)). { intro. apply Hrem. apply Z.mod_divide; lia. }
          destruct (Z.eq_dec d k).
          -- subst. contradiction.
          -- apply IHfuel with (d + 1); try lia.
             assumption.
  Qed.

  Lemma check_prime_sound : forall p,
    check_prime p = true -> prime p.
  Proof.
    intros p Hchk.
    unfold check_prime in Hchk.
    destruct (p <=? 1) eqn:Hle. { discriminate. }
    apply Z.leb_nle in Hle.
    apply prime_alt. split; try lia.
    intros n [Hn1 Hnp] Hdiv.
    assert (Hsq: n * n <= p \/ n * n > p) by lia.
    destruct Hsq.
    - eapply check_divisors_sound in Hchk; try eassumption; try lia.
    - destruct Hdiv as [k Hk].
      assert (k * k <= p).
      {
        assert (k * n = p) by (rewrite Hk; ring).
        assert (k < n).
        { destruct (Z.ge_le_dec k n); try lia.
          assert (k * n >= n * n). { apply Z.mul_le_mono_nonneg_r; lia. }
          lia. }
        assert (k * k < n * n). { apply Z.mul_lt_mono_nonneg; lia. }
        lia.
      }
      assert (Hk2: 2 <= k).
      {
         destruct (Z_le_gt_dec 2 k); try assumption.
         assert (k <= 1) by lia.
         assert (k >= 1). 
         { destruct (Z_le_gt_dec 1 k); try assumption.
           assert (k <= 0) by lia.
           rewrite Hk in Hle.
           assert (p <= 0). 
           { apply Z.mul_nonpos_nonneg; lia. }
           lia.
         }
         assert (k = 1) by lia.
         subst. rewrite Z.mul_1_l in Hk. subst. lia.
      }
      eapply check_divisors_sound in Hchk; try eassumption; try lia.
      exists n. rewrite Z.mul_comm. assumption.
  Qed.

  Close Scope Z_scope.
End ZPrimality.

Example test_factorize_big : factorize_spec 1003001001 [3; 31; 10784957].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    (* Use Z for large number multiplication check *)
    apply Nat2Z.inj.
    repeat rewrite Nat2Z.inj_mul.
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 3 *)
        apply Z_prime_to_nat_prime; try lia.
        apply check_prime_sound. vm_compute. reflexivity.
      * (* is_prime 31 *)
        apply Z_prime_to_nat_prime; try lia.
        apply check_prime_sound. vm_compute. reflexivity.
      * (* is_prime 10784957 *)
        apply Z_prime_to_nat_prime; try lia.
        apply check_prime_sound. vm_compute. reflexivity.
    + (* Part 3: Sorted check *)
      repeat constructor; try lia.
Qed.