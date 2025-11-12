Require Import Coq.Arith.Arith.

Open Scope nat_scope.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S 0 => 1
  | S (S n') => fib (S n') + fib n'
  end.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime (n : nat) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d < n -> ~ divides d n.

Inductive count_prime_fib_up_to : nat -> nat -> Prop :=
| cpfu_0 : count_prime_fib_up_to 0 0
| cpfu_step_nonprime :
    forall k n,
      count_prime_fib_up_to k n ->
      ~ is_prime (fib (S k)) ->
      count_prime_fib_up_to (S k) n
| cpfu_step_prime :
    forall k n,
      count_prime_fib_up_to k n ->
      is_prime (fib (S k)) ->
      count_prime_fib_up_to (S k) (S n).

Definition prime_fib_spec (n : nat) (p : nat) : Prop :=
  exists k, count_prime_fib_up_to k n /\ is_prime (fib k) /\ p = fib k.