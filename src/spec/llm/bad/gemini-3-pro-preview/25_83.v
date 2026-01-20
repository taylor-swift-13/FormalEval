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

Fixpoint no_divisors_Z (p : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f =>
    if (d >=? p)%Z then true
    else if (Z.rem p d =? 0)%Z then false
    else no_divisors_Z p (d + 1)%Z f
  end.

Definition check_prime (p : nat) : bool :=
  if p <=? 1 then false
  else no_divisors_Z (Z.of_nat p) 2 (p - 2).

Lemma no_divisors_Z_sound : forall p d fuel,
  (0 < d)%Z ->
  no_divisors_Z p d fuel = true ->
  forall k : Z, (d <= k < d + Z.of_nat fuel)%Z ->
  (k < p)%Z ->
  ~ (Z.divide k p).
Proof.
  induction fuel; intros.
  - simpl in H1. lia.
  - simpl in H0.
    destruct (d >=? p)%Z eqn:Hge.
    + apply Z.leb_le in Hge. lia.
    + destruct (Z.rem p d =? 0)%Z eqn:Hrem.
      * discriminate.
      * apply Z.eqb_neq in Hrem.
        assert (~ (Z.divide d p)).
        { intro. apply Z.rem_divide in H4; try lia. congruence. }
        assert (k = d \/ d < k)%Z by lia.
        destruct H5.
        -- subst. assumption.
        -- apply IHfuel with (d := (d + 1)%Z); try lia.
           assumption.
           assert (Z.of_nat (S fuel) = Z.of_nat fuel + 1)%Z by lia.
           rewrite H6 in H1. lia.
           assumption.
Qed.

Lemma check_prime_correct : forall p, check_prime p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime in H.
  destruct (p <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    split; try assumption.
    intros d Hd.
    destruct (d =? 1) eqn:Heq1.
    + left. apply Nat.eqb_eq. assumption.
    + destruct (d =? p) eqn:Heqp.
      * right. apply Nat.eqb_eq. assumption.
      * apply Nat.eqb_neq in Heq1.
        apply Nat.eqb_neq in Heqp.
        assert (1 < d < p) by (split; try lia; apply Nat.divide_pos_le in Hd; try lia).
        exfalso.
        apply Nat2Z.inj_divide in Hd.
        assert (Hrange: (2 <= Z.of_nat d < 2 + Z.of_nat (p - 2))%Z).
        { split. lia. replace (2 + Z.of_nat (p - 2))%Z with (Z.of_nat p) by lia. lia. }
        apply no_divisors_Z_sound with (k := Z.of_nat d) in H; try lia.
Qed.

Example test_factorize_123456786 : factorize_spec 123456786 [2; 3; 20576131].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
    + repeat constructor.
      * apply Nat.leb_le. vm_compute. reflexivity.
      * apply Nat.leb_le. vm_compute. reflexivity.
Qed.