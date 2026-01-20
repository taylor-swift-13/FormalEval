
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Factorial.

Definition special_factorial_spec (n : nat) (result : nat) : Prop :=
  n > 0 ->
  result = fold_left (fun acc i => acc * fact i) (seq 1 n) 1.
