Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper definitions for primality checking by computation *)
Fixpoint check_divisors (d n fuel : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    if Nat.eqb d n then true
    else if Nat.eqb (n mod d) 0 then false
    else check_divisors (S d) n fuel'
  end.

Definition check_prime (n : nat) : bool :=
  if Nat.leb n 1 then false else check_divisors 2 n n.

Lemma check_divisors_correct : forall fuel d n,
  2 <= d -> n <= d + fuel ->
  check_divisors d n fuel = true ->
  (forall k, d <= k < n -> ~ Nat.divide k n).
Proof.
  induction fuel; intros.
  - lia.
  - simpl in H1.
    destruct (Nat.eqb d n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. lia.
    + destruct (Nat.eqb (n mod d) 0) eqn:Hmod.
      * discriminate.
      * apply Nat.eqb_neq in Heq.
        apply Nat.eqb_neq in Hmod.
        intros k Hk.
        destruct (Nat.eq_dec k d).
        -- subst. intro Hdiv. apply Nat.mod_divide in Hdiv; auto. lia.
        -- apply IHfuel with (d := S d).
           ++ lia.
           ++ lia.
           ++ assumption.
           ++ lia.
Qed.

Lemma check_prime_correct : forall n, check_prime n = true -> is_prime n.
Proof.
  intros n H.
  unfold check_prime in H.
  destruct (Nat.leb n 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_nle in Hle.
    split.
    + lia.
    + intros d Hdiv.
      destruct (Nat.eq_dec d 1); auto.
      destruct (Nat.eq_dec d n); auto.
      assert (1 < d < n).
      { split.
        - destruct d; try lia. destruct d; try lia.
          destruct Hdiv. rewrite Nat.mul_0_r in H0. discriminate.
        - apply Nat.divide_pos_le in Hdiv; lia.
      }
      exfalso.
      apply (check_divisors_correct n 2 n); auto.
      * lia.
      * lia.
      * lia.
      * assumption.
Qed.

Example test_factorize_1028 : factorize_spec 1028 [2; 2; 257].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    simpl. reflexivity.
  - split.
    + (* Primality check *)
      repeat constructor.
      * apply check_prime_correct; reflexivity.
      * apply check_prime_correct; reflexivity.
      * apply check_prime_correct; reflexivity.
    + (* Sorted check *)
      repeat constructor; simpl; try lia.
Qed.