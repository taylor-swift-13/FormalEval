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

(* Helper definitions and lemmas for primality checking *)
Fixpoint check_divisors (n d k : nat) : bool :=
  match k with
  | 0 => true
  | S k' => if n mod d =? 0 then false else check_divisors n (S d) k'
  end.

Definition is_prime_b (n : nat) : bool :=
  if n <=? 1 then false else check_divisors n 2 (n - 2).

Lemma check_divisors_correct : forall n d k,
  d > 0 ->
  check_divisors n d k = true ->
  forall x, d <= x < d + k -> ~ Nat.divide x n.
Proof.
  induction k; simpl; intros.
  - lia.
  - destruct (n mod d =? 0) eqn:Heq.
    + discriminate.
    + apply Nat.eqb_neq in Heq.
      intros x Hrange Hdiv.
      destruct (Nat.eq_dec x d).
      * subst. apply Nat.mod_divide in Hdiv; auto.
      * apply IHk; auto. lia. lia.
Qed.

Lemma is_prime_b_correct : forall n, is_prime_b n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_b in H.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    split; auto.
    intros d Hdiv.
    destruct (Nat.eq_dec d 1); auto.
    destruct (Nat.eq_dec d n); auto.
    exfalso.
    assert (1 < d < n).
    { split.
      - destruct d; try lia. destruct d; try lia.
        apply Nat.divide_pos_le in Hdiv; lia.
      - apply Nat.divide_pos_le in Hdiv; lia.
    }
    apply (check_divisors_correct n 2 (n - 2)); auto.
    + lia.
    + lia.
Qed.

Example test_factorize_large : factorize_spec 112234364 [2; 2; 11; 643; 3967].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    simpl. reflexivity.
  - split.
    + (* Primality check *)
      repeat (apply Forall_cons; [ apply is_prime_b_correct; vm_compute; reflexivity | ]).
      apply Forall_nil.
    + (* Sorted check *)
      repeat (constructor; try lia).
Qed.