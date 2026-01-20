
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint fib4_func (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 0
  | S (S O) => 2
  | S (S (S O)) => 0
  | S (S (S (S n'))) => 
      fib4_func (S (S (S n'))) + fib4_func (S (S n')) + fib4_func (S n') + fib4_func n'
  end.

Definition fib4_spec (n : nat) (result : Z) : Prop :=
  result = fib4_func n.
