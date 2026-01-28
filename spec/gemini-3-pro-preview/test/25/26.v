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

Example test_factorize_13 : factorize_spec 13 [13].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 13 *)
        unfold is_prime. split.
        -- (* 13 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [| d].
           { (* d = 0 *) destruct Hdiv as [x Hx]. rewrite Nat.mul_0_r in Hx. discriminate. }
           destruct d as [| d].
           { (* d = 1 *) left. reflexivity. }
           (* d >= 2 *)
           (* Check d = 2 to 12 *)
           do 11 (destruct d as [| d]; [ 
             exfalso; 
             apply Nat.mod_divide in Hdiv; [ simpl in Hdiv; discriminate | lia ] 
           | ]).
           (* d = 13 *)
           destruct d as [| d].
           { right. reflexivity. }
           (* d > 13 *)
           exfalso. apply Nat.divide_pos_le in Hdiv; lia.
      * (* End of list *)
        constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.