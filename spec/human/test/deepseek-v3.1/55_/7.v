Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_0_pre (b : bool) : Prop := True.

Definition problem_0_spec (b : bool) (res : nat) : Prop :=
  match b with
  | false => res = 0
  | true => exists n, is_fib n res
  end.

Example problem_0_input_false : problem_0_spec false 0.
Proof.
  unfold problem_0_spec.
  reflexivity.
Qed.