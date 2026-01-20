
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Open Scope Z_scope.

Fixpoint fib4_seq (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | 1%nat => 0
  | 2%nat => 2
  | 3%nat => 0
  | S (S (S (S m))) => fib4_seq (S (S (S m))) + fib4_seq (S (S m)) + fib4_seq (S m) + fib4_seq m
  end.

Definition fib4_spec (n : Z) (res : Z) : Prop :=
  n >= 0 /\ res = fib4_seq (Z.to_nat n).
