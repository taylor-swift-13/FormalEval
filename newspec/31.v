(* Return true if a given number is prime, and false otherwise.
>>> is_prime(6)
False
>>> is_prime(101)
True
>>> is_prime(11)
True
>>> is_prime(13441)
True
>>> is_prime(61)
True
>>> is_prime(4)
False
>>> is_prime(1)
False
*)

(* Spec(input : int, output : bool) :=

​	output = prime(input) *)


Require Import Arith.

(* Pre: no additional constraints for `is_prime` by default *)
Definition Pre (n : nat) : Prop := True.
Definition Spec (n : nat) (output : bool) : Prop :=
  (1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n)) <-> output = true.
  

