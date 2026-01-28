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

Example test_factorize_1024 : factorize_spec 1024 [2; 2; 2; 2; 2; 2; 2; 2; 2; 2].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      assert (H2: is_prime 2).
      {
        unfold is_prime. split.
        - lia.
        - intros d Hdiv.
          destruct d as [| [| [| d'] ]].
          + destruct Hdiv as [z Hz].
            rewrite Nat.mul_0_r in Hz.
            discriminate.
          + left. reflexivity.
          + right. reflexivity.
          + apply Nat.divide_pos_le in Hdiv; try lia.
      }
      repeat (constructor; try exact H2).
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.