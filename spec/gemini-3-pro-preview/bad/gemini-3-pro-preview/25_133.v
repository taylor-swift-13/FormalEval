Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper definitions for primality checking *)

Fixpoint no_divisor (n : nat) (d : nat) (fuel : nat) : bool :=
  match fuel with
  | 0 => true 
  | S f => 
      if d * d >? n then true
      else if Nat.eqb (n mod d) 0 then false
      else no_divisor n (S d) f
  end.

Lemma no_divisor_correct : forall n d fuel,
  d > 1 ->
  no_divisor n d fuel = true ->
  (forall x, d <= x -> x < d + fuel -> x * x <= n -> ~ Nat.divide x n).
Proof.
  induction fuel; intros.
  - intros. lia.
  - simpl in H0.
    destruct (d * d >? n) eqn:Hsq.
    + intros. apply Nat.leb_gt in Hsq.
      assert (x * x > n).
      { apply Nat.lt_le_trans with (d * d); auto.
        apply Nat.mul_le_mono; lia. }
      lia.
    + destruct (Nat.eqb (n mod d) 0) eqn:Hrem.
      * discriminate.
      * apply Nat.eqb_neq in Hrem.
        intros x Hle Hlt Hxsq Hdiv.
        destruct (Nat.eq_dec x d).
        -- subst. apply Nat.mod_divide in Hdiv; auto. congruence.
        -- apply IHfuel with (S d); auto.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ auto.
Qed.

Lemma prime_check_correct : forall n, 
  n > 1 -> 
  no_divisor n 2 n = true -> 
  is_prime n.
Proof.
  intros n Hn Hchk.
  split; auto.
  intros d Hd.
  destruct (le_lt_dec (d * d) n).
  - destruct (Nat.eq_dec d 1); auto.
    destruct (Nat.eq_dec d n); auto.
    assert (Hrange: 2 <= d < 2 + n).
    { split. 
      - destruct d; try lia. destruct d; try lia. auto.
      - lia.
    }
    exfalso.
    apply (no_divisor_correct n 2 n); auto.
    + lia.
    + lia.
    + lia.
    + auto.
    + assumption.
  - assert (exists q, n = d * q). apply Hd. destruct H as [q Hq].
    destruct (Nat.eq_dec q 1).
    + subst. rewrite Nat.mul_1_r in Hq. right. symmetry. auto.
    + assert (q * q <= n).
      {
         destruct (le_lt_dec (q * q) n); auto.
         assert (d * q > n).
         { 
           apply Nat.nle_gt in l.
           apply Nat.nle_gt in H0.
           assert (n * n < (d * d) * (q * q)).
           { apply Nat.mul_lt_mono; auto. }
           rewrite <- Nat.mul_shuffle0 in H1.
           rewrite <- Hq in H1.
           rewrite <- Hq in H1.
           lia.
         }
         subst n. lia.
      }
      assert (1 < q).
      { destruct q; try lia. destruct q; try lia. auto. }
      assert (Hrange: 2 <= q < 2 + n) by lia.
      exfalso.
      apply (no_divisor_correct n 2 n); auto.
      * lia.
      * lia.
      * lia.
      * auto.
      * exists d. rewrite Nat.mul_comm. auto.
Qed.

Example test_factorize_big : factorize_spec (Z.to_nat 987654326) [Z.to_nat 2; Z.to_nat 131; Z.to_nat 3769673].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    (* Use Z to avoid large unary nat construction *)
    rewrite <- Z2Nat.inj_mul by lia.
    rewrite <- Z2Nat.inj_mul by lia.
    simpl fold_right.
    rewrite Nat.mul_1_r.
    apply Z2Nat.inj_iff; try lia.
    reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * apply prime_check_correct; [lia | vm_compute; reflexivity].
      * constructor.
        -- apply prime_check_correct; [lia | vm_compute; reflexivity].
        -- constructor.
           ++ apply prime_check_correct; [lia | vm_compute; reflexivity].
           ++ constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.