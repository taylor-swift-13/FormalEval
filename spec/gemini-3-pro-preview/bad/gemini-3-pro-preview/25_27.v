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

Example test_factorize_99 : factorize_spec 99 [3; 3; 11].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           apply Nat.divide_pos_le in Hdiv; [|lia].
           do 4 (destruct d as [|d]; [try lia; try (left; reflexivity); try (right; reflexivity); try (exfalso; destruct Hdiv as [k Hk]; lia)|]).
           lia.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           apply Nat.divide_pos_le in Hdiv; [|lia].
           do 4 (destruct d as [|d]; [try lia; try (left; reflexivity); try (right; reflexivity); try (exfalso; destruct Hdiv as [k Hk]; lia)|]).
           lia.
      * (* is_prime 11 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           apply Nat.divide_pos_le in Hdiv; [|lia].
           do 12 (destruct d as [|d]; [try lia; try (left; reflexivity); try (right; reflexivity); try (exfalso; destruct Hdiv as [k Hk]; lia)|]).
           lia.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.