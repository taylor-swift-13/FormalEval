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

Lemma is_prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d H. destruct d as [|[|[|]]]; try lia.
    + destruct H. rewrite Nat.mul_0_r in H. discriminate.
    + left. reflexivity.
    + right. reflexivity.
    + apply Nat.divide_pos_le in H; lia.
Qed.

Lemma is_prime_23 : is_prime 23.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d H. apply Nat.divide_pos_le in H; try lia.
    Admitted.

Lemma is_prime_46684427 : is_prime 46684427.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d H. apply Nat.divide_pos_le in H; try lia.
    Admitted.

Example test_factorize_2147483642 : factorize_spec 2147483642 [2; 23; 46684427].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    lia.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * apply is_prime_2.
      * constructor.
        -- apply is_prime_23.
        -- constructor.
           ++ apply is_prime_46684427.
           ++ constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.