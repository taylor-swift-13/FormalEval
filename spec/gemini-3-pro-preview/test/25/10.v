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

Example test_factorize_15 : factorize_spec 15 [3; 5].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- (* 3 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [| [| [| [| d'] ]]].
           ++ (* d = 0 *)
              destruct Hdiv as [z Hz].
              rewrite Nat.mul_0_r in Hz.
              discriminate.
           ++ (* d = 1 *)
              left. reflexivity.
           ++ (* d = 2 *)
              destruct Hdiv as [z Hz].
              lia.
           ++ (* d = 3 *)
              right. reflexivity.
           ++ (* d >= 4 *)
              apply Nat.divide_pos_le in Hdiv; try lia.
      * constructor.
        -- (* is_prime 5 *)
           unfold is_prime. split.
           ++ (* 5 > 1 *)
              lia.
           ++ (* Divisors check *)
              intros d Hdiv.
              destruct d as [| [| [| [| [| [| d'] ]]]]].
              ** (* d = 0 *)
                 destruct Hdiv as [z Hz].
                 rewrite Nat.mul_0_r in Hz.
                 discriminate.
              ** (* d = 1 *)
                 left. reflexivity.
              ** (* d = 2 *)
                 destruct Hdiv as [z Hz]. lia.
              ** (* d = 3 *)
                 destruct Hdiv as [z Hz]. lia.
              ** (* d = 4 *)
                 destruct Hdiv as [z Hz]. lia.
              ** (* d = 5 *)
                 right. reflexivity.
              ** (* d >= 6 *)
                 apply Nat.divide_pos_le in Hdiv; try lia.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.