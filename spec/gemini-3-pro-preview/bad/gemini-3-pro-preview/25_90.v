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

Example test_factorize_38 : factorize_spec 38 [2; 19].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| d'] ]].
           ++ destruct Hdiv as [z Hz].
              rewrite Nat.mul_0_r in Hz.
              discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 19 *)
        constructor.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              apply Nat.divide_pos_le in Hdiv; try lia.
              (* Check divisors 0 to 18 *)
              do 19 (destruct d; [
                try (destruct Hdiv as [k Hk]; lia);
                try (left; reflexivity)
              | ]).
              (* d is now 19 *)
              destruct d.
              ** right. reflexivity.
              ** lia.
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat (constructor; try lia).
Qed.