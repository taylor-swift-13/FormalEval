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

Lemma is_prime_123456791 : is_prime 123456791.
Proof. Admitted.

Example test_factorize_123456791 : factorize_spec 123456791 [123456791].
Proof.
  unfold factorize_spec.
  split.
  - unfold fold_right. rewrite Nat.mul_1_r. reflexivity.
  - split.
    + constructor.
      * apply is_prime_123456791.
      * constructor.
    + repeat constructor.
Qed.