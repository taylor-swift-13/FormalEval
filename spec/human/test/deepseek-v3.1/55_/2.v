Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_1_pre (n : nat) : Prop := True.

Definition problem_1_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

Example fib_1_example : problem_1_spec 1 1.
Proof.
  unfold problem_1_spec.
  apply fib_one.
Qed.