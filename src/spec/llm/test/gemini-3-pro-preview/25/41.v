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

Example test_factorize_39 : factorize_spec 39 [3; 13].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hd.
           do 4 (destruct d as [|d]; [
             try (left; reflexivity);
             try (right; reflexivity);
             try (destruct Hd as [x Hx]; simpl in Hx; lia)
           | ]).
           apply Nat.divide_pos_le in Hd; lia.
      * constructor.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hd.
              do 14 (destruct d as [|d]; [
                try (left; reflexivity);
                try (right; reflexivity);
                try (destruct Hd as [x Hx]; simpl in Hx; lia)
              | ]).
              apply Nat.divide_pos_le in Hd; lia.
        -- constructor.
    + repeat constructor; lia.
Qed.