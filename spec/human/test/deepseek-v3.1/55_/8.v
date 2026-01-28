Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_1_pre (b : bool) : Prop := True.

Definition problem_1_spec (b : bool) (res : nat) : Prop :=
  match b with
  | true => res = 1
  | false => res = 0
  end.

Example problem_1_test_true : problem_1_spec true 1.
Proof.
  unfold problem_1_spec.
  reflexivity.
Qed.

Example problem_1_test_false : problem_1_spec false 0.
Proof.
  unfold problem_1_spec.
  reflexivity.
Qed.