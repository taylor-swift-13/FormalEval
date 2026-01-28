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

Example test_factorize_58 : factorize_spec 58 [2; 29].
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
           ++ destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; try lia.
      * constructor.
        -- (* is_prime 29 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              apply Nat.divide_pos_le in Hdiv; try lia.
              destruct d as [|d]. { lia. } (* 0 *)
              destruct d as [|d]. { left. reflexivity. } (* 1 *)
              (* Check 2..28 *)
              do 27 (destruct d as [|d]; [ destruct Hdiv as [k Hk]; lia | ]).
              (* 29 *)
              destruct d as [|d].
              ** right. reflexivity.
              ** lia.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor. lia.
Qed.