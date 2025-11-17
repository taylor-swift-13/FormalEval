(* def is_multiply_prime(a):
"""Write a function that returns true if the given number is the multiplication of 3 prime numbers
and false otherwise.
Knowing that (a) is less then 100.
Example:
is_multiply_prime(30) == True
30 = 2 * 3 * 5
""" *)
Require Import Arith.


(* 定义：一个数 n 是素数 *)
Definition is_prime (n : nat) : Prop :=
  n > 1 /\ forall d : nat, d mod n = 0 -> d = 1 \/ d = n.

Definition Pre (a : nat) : Prop := (a < 100)%nat.

Definition is_multiply_prime_spec (a : nat) (b : bool) : Prop :=
  (a < 100) ->
  (b = true <-> exists p1 p2 p3, is_prime p1 /\ is_prime p2 /\ is_prime p3 /\ a = p1 * p2 * p3).

