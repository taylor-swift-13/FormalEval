
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Definition fib4_spec (n : nat) (result : nat) : Prop :=
  (n = 0 /\ result = 0) \/
  (n = 1 /\ result = 0) \/
  (n = 2 /\ result = 2) \/
  (n = 3 /\ result = 0) \/
  (n >= 4 /\ exists a b c d : nat,
    a = 0 /\ b = 0 /\ c = 2 /\ d = 0 /\
    (forall i, 4 <= i <= n -> 
      let a' := b in
      let b' := c in
      let c' := d in
      let d' := a + b + c + d in
      a = a' /\ b = b' /\ c = c' /\ d = d' /\
      a + b + c + d = fib4_spec i d') /\
    result = d).
