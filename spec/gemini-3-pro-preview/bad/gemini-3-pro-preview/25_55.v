Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 < d -> (d | p) -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

(* Helper definitions and lemmas for primality testing on Z *)

Fixpoint no_divisor_in_range (p : Z) (d : Z) (count : nat) : bool :=
  match count with
  | O => true
  | S c => 
      if (d * d >? p) then true
      else if (p mod d =? 0) then false
      else no_divisor_in_range p (d + 1) c
  end.

Lemma no_divisor_in_range_correct : forall count p d,
  0 < d ->
  no_divisor_in_range p d count = true ->
  forall k, d <= k < d + Z.of_nat count -> ~(k | p) \/ k * k > p.
Proof.
  induction count; intros p d Hd Hcheck k Hk.
  - simpl in Hk. lia.
  - simpl in Hcheck.
    destruct (d * d >? p) eqn:Hsq.
    + apply Z.gtb_lt in Hsq. right.
      assert (d <= k) by lia.
      apply Z.lt_le_trans with (d*d); try lia.
      apply Z.mul_le_mono_nonneg; lia.
    + destruct (p mod d =? 0) eqn:Hmod.
      * discriminate.
      * apply Z.eqb_neq in Hmod.
        assert (Hnd: ~(d | p)).
        { intro Hdiv. apply Z.mod_divide in Hdiv; try lia. contradiction. }
        rewrite Nat2Z.inj_succ in Hk.
        destruct (Z.eq_dec d k).
        -- subst. left. assumption.
        -- apply IHcount with (d := d + 1).
           ++ lia.
           ++ assumption.
           ++ lia.
Qed.

Definition check_prime (p : Z) : bool :=
  if (p <=? 1) then false
  else no_divisor_in_range p 2 (Z.to_nat (Z.sqrt p) + 2).

Lemma check_prime_correct : forall p, check_prime p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime in H.
  destruct (p <=? 1) eqn:Hle. { discriminate. }
  apply Z.leb_gt in Hle.
  unfold is_prime. split; [assumption|].
  intros d Hpos Hdiv.
  destruct (Z.eq_dec d 1). { left. assumption. }
  destruct (Z.eq_dec d p). { right. assumption. }
  
  (* Assume d is a proper divisor *)
  assert (Hproper: 1 < d < p).
  { split; try lia. apply Z.divide_pos_le in Hdiv; lia. }
  
  (* There exists a prime factor q <= sqrt(p) *)
  (* We just need existence of *some* divisor q <= sqrt(p) *)
  assert (exists q, 1 < q /\ q * q <= p /\ (q | p)).
  {
    destruct (Z.le_gt_cases (d * d) p).
    - exists d. split; [lia|]. split; [assumption|assumption].
    - exists (p / d).
      assert (Hdiv': p = (p / d) * d). { apply Z.div_exact; try lia. assumption. }
      split.
      + assert (p / d * d = p). { apply sym_eq. assumption. }
        assert (p / d > 1).
        {
           destruct (Z.le_gt_cases (p/d) 1).
           - assert (p/d * d <= 1 * d). { apply Z.mul_le_mono_nonneg_r; lia. }
             rewrite H0 in H1. lia.
           - assumption.
        }
        assumption.
      + split.
        * assert (p/d < d).
          {
             assert (p/d * d < d * d). { rewrite <- Hdiv'. assumption. }
             apply Z.mul_lt_mono_pos_r in H0; lia.
          }
          apply Z.le_trans with ((p/d) * d).
          -- apply Z.mul_le_mono_nonneg_l; try lia.
             apply Z.lt_le_incl. assumption.
          -- rewrite <- Hdiv'. apply Z.le_refl.
        * exists d. rewrite Z.mul_comm. apply sym_eq. assumption.
  }
  destruct H0 as [q [Hq1 [Hq2 Hqdiv]]].
  
  (* q should have been found by check_prime *)
  assert (Hcheck: no_divisor_in_range p 2 (Z.to_nat (Z.sqrt p) + 2) = true).
  { assumption. }
  
  assert (Hnone: forall k, 2 <= k < 2 + Z.of_nat (Z.to_nat (Z.sqrt p) + 2) -> ~(k | p) \/ k * k > p).
  { apply no_divisor_in_range_correct; try lia. assumption. }
  
  specialize (Hnone q).
  assert (Hrange: 2 <= q < 2 + Z.of_nat (Z.to_nat (Z.sqrt p) + 2)).
  {
    split; [lia|].
    apply Z.lt_le_trans with (Z.sqrt p + 1).
    - apply Z.lt_succ_r. apply Z.sqrt_le_mono. assumption.
    - rewrite Z2Nat.id; try (apply Z.sqrt_nonneg). lia.
  }
  apply Hnone in Hrange.
  destruct Hrange.
  - contradiction.
  - lia.
Qed.

Example test_factorize_big : factorize_spec 9999999966 [2; 3; 11; 457; 331543].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Primality check *)
      repeat constructor; apply check_prime_correct; vm_compute; reflexivity.
    + (* Sorted check *)
      repeat (constructor; try lia).
Qed.