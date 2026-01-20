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

Ltac prove_prime_small :=
  unfold is_prime; split; [ lia |
    intros d Hdiv;
    apply Nat.divide_pos_le in Hdiv; try lia;
    do 35 (
      destruct d;
      [
        try (left; reflexivity);
        try (right; reflexivity);
        try (destruct Hdiv as [k Hk]; simpl in Hk; lia)
      |
      ]
    );
    lia
  ].

Example test_factorize_1023 : factorize_spec 1023 [3; 11; 31].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor; [ prove_prime_small | ].
      constructor; [ prove_prime_small | ].
      constructor; [ prove_prime_small | ].
      constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.