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

Example test_factorize_14 : factorize_spec 14 [2; 7].
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
        -- (* 2 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [| [| [| d'] ]].
           ++ (* d = 0 *)
              destruct Hdiv as [z Hz].
              simpl in Hz. lia.
           ++ (* d = 1 *)
              left. reflexivity.
           ++ (* d = 2 *)
              right. reflexivity.
           ++ (* d >= 3 *)
              apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 7 *)
        constructor.
        -- (* is_prime 7 *)
           unfold is_prime. split.
           ++ (* 7 > 1 *)
              lia.
           ++ (* Divisors check *)
              intros d Hdiv.
              (* Check d = 0, 1, ..., 7, >7 *)
              destruct d as [| d]. { destruct Hdiv as [z Hz]; simpl in Hz; lia. }
              destruct d as [| d]. { left. reflexivity. } (* 1 *)
              destruct d as [| d]. { exfalso. destruct Hdiv as [z Hz]. lia. } (* 2 *)
              destruct d as [| d]. { exfalso. destruct Hdiv as [z Hz]. lia. } (* 3 *)
              destruct d as [| d]. { exfalso. destruct Hdiv as [z Hz]. lia. } (* 4 *)
              destruct d as [| d]. { exfalso. destruct Hdiv as [z Hz]. lia. } (* 5 *)
              destruct d as [| d]. { exfalso. destruct Hdiv as [z Hz]. lia. } (* 6 *)
              destruct d as [| d]. { right. reflexivity. } (* 7 *)
              (* d >= 8 *)
              apply Nat.divide_pos_le in Hdiv; lia.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.