Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper functions and lemmas for efficient primality checking *)

Fixpoint check_range (n d k : nat) : bool :=
  match k with
  | 0 => true
  | S k' => 
    if Nat.eqb (n mod d) 0 then false
    else check_range n (S d) k'
  end.

Lemma check_range_correct : forall n d k,
  d > 0 ->
  check_range n d k = true ->
  forall x, d <= x < d + k -> ~ Nat.divide x n.
Proof.
  induction k; simpl; intros.
  - lia.
  - destruct (Nat.eqb_spec (n mod d) 0).
    + discriminate.
    + apply IHk with (x:=x) in H0; try lia.
      destruct (Nat.eq_dec x d).
      * subst. intro C. apply Nat.mod_divide in C; try lia. contradiction.
      * assumption.
Qed.

Lemma prime_check_sound : forall n,
  n > 1 ->
  check_range n 2 (n - 2) = true ->
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  unfold is_prime. split; auto.
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); auto.
  destruct (Nat.eq_dec d n); auto.
  exfalso.
  assert (Hrange: 2 <= d < 2 + (n - 2)).
  {
    split.
    * destruct d; try lia. destruct d; try lia.
    * apply Nat.divide_pos_le in Hdiv; lia.
  }
  eapply check_range_correct in Hcheck; eauto.
  - apply Hcheck in Hrange. contradiction.
  - lia.
Qed.

Example test_factorize_999977 : factorize_spec 999977 [11; 90907].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 11 *)
        apply prime_check_sound; try lia.
        vm_compute. reflexivity.
      * (* is_prime 90907 *)
        constructor.
        -- apply prime_check_sound; try lia.
           vm_compute. reflexivity.
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; simpl; try lia.
Qed.