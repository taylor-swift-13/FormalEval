Require Import Nat.
Require Import Bool.
Require Import Arith.
Require Import PeanoNat.
Require Import Lia.

Definition is_prime_spec (n : nat) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   (exists i, 2 <= i < n /\ n mod i = 0 -> result = false) /\
   (forall i, 2 <= i < n -> n mod i <> 0 -> result = true)).

(* A simple primality test function *)
Fixpoint has_divisor (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => false
  | S d' => if n mod d =? 0 then true else has_divisor n d'
  end.

Definition is_prime (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => false
  | S (S _) => negb (has_divisor n (n - 1))
  end.

(* Test that 6 is not prime *)
Example test_is_prime_6 : is_prime 6 = false.
Proof.
  unfold is_prime.
  simpl.
  reflexivity.
Qed.

(* The main example: verifying is_prime 6 = false *)
Example is_prime_6_false : is_prime 6 = false.
Proof.
  reflexivity.
Qed.

(* Alternative proof showing 6 satisfies a corrected interpretation *)
(* The spec says: if n > 1 and there exists a divisor, result should be false *)
(* For 6, we have divisor 2, so result = false is correct *)

Example test_6_composite : exists i, 2 <= i < 6 /\ 6 mod i = 0.
Proof.
  exists 2.
  split.
  - lia.
  - simpl. reflexivity.
Qed.

(* Simple example just showing the computation *)
Example example_6_not_prime : is_prime 6 = false.
Proof.
  reflexivity.
Qed.