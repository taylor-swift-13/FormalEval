
Require Import Coq.Arith.PeanoNat.

Definition is_multiply_prime_spec (a : nat) (res : bool) : Prop :=
  res = true <-> 
  (exists p1 p2 p3 : nat, 
    Nat.Prime p1 /\ Nat.Prime p2 /\ Nat.Prime p3 /\ a = p1 * p2 * p3).
