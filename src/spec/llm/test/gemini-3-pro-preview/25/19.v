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

Example test_factorize_1025 : factorize_spec 1025 [5; 5; 41].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 5 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           do 6 (destruct d as [|d]; [
             try (left; reflexivity);
             try (right; reflexivity);
             try (exfalso; destruct Hdiv as [x Hx]; lia)
           | ]).
           apply Nat.divide_pos_le in Hdiv; lia.
      * constructor.
        -- (* is_prime 5 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              do 6 (destruct d as [|d]; [
                try (left; reflexivity);
                try (right; reflexivity);
                try (exfalso; destruct Hdiv as [x Hx]; lia)
              | ]).
              apply Nat.divide_pos_le in Hdiv; lia.
        -- constructor.
           ++ (* is_prime 41 *)
              unfold is_prime. split.
              ** lia.
              ** intros d Hdiv.
                 do 42 (destruct d as [|d]; [
                   try (left; reflexivity);
                   try (right; reflexivity);
                   try (exfalso; destruct Hdiv as [x Hx]; lia)
                 | ]).
                 apply Nat.divide_pos_le in Hdiv; lia.
           ++ constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.