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

Example test_factorize_18 : factorize_spec 18 [2; 3; 3].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- (* 2 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [| [| [| d'] ]].
           ++ (* d = 0 *)
              apply Nat.divide_0_l in Hdiv. discriminate.
           ++ (* d = 1 *)
              left. reflexivity.
           ++ (* d = 2 *)
              right. reflexivity.
           ++ (* d >= 3 *)
              apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- (* 3 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [| [| [| [| d'] ]]].
           ++ (* d = 0 *)
              apply Nat.divide_0_l in Hdiv. discriminate.
           ++ (* d = 1 *)
              left. reflexivity.
           ++ (* d = 2 *)
              destruct Hdiv as [k Hk].
              destruct k as [| [| k']]; simpl in Hk; try discriminate.
              lia.
           ++ (* d = 3 *)
              right. reflexivity.
           ++ (* d >= 4 *)
              apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- (* 3 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [| [| [| [| d'] ]]].
           ++ (* d = 0 *)
              apply Nat.divide_0_l in Hdiv. discriminate.
           ++ (* d = 1 *)
              left. reflexivity.
           ++ (* d = 2 *)
              destruct Hdiv as [k Hk].
              destruct k as [| [| k']]; simpl in Hk; try discriminate.
              lia.
           ++ (* d = 3 *)
              right. reflexivity.
           ++ (* d >= 4 *)
              apply Nat.divide_pos_le in Hdiv; try lia.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.