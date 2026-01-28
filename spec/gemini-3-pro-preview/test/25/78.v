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

Example test_factorize_101 : factorize_spec 101 [101].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d [k Hk].
           assert (Heq : d * k = 101) by lia.
           destruct (le_lt_dec d 10) as [Hd_small | Hd_large].
           ++ do 11 (destruct d as [|d]; [ try (left; lia); try (right; lia); try lia | ]).
              lia.
           ++ destruct (le_lt_dec k 10) as [Hk_small | Hk_large].
              ** do 11 (destruct k as [|k]; [ try (left; lia); try (right; lia); try lia | ]).
                 lia.
              ** assert (Hprod : d * k >= 11 * 11).
                 { apply Nat.mul_le_mono; lia. }
                 lia.
      * constructor.
    + repeat constructor.
Qed.