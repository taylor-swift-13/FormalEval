Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_3_pre (n : nat) : Prop := True.

Definition problem_3_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

(* Helper lemmas for proving fib(4) = 3 *)
Lemma fib_2 : is_fib 2 1.
Proof.
  apply fib_step with (n := 0) (res_n := 0) (res_n1 := 1).
  - apply fib_zero.
  - apply fib_one.
Qed.

Lemma fib_3 : is_fib 3 2.
Proof.
  apply fib_step with (n := 1) (res_n := 1) (res_n1 := 1).
  - apply fib_one.
  - apply fib_2.
Qed.

Lemma fib_4 : is_fib 4 3.
Proof.
  apply fib_step with (n := 2) (res_n := 1) (res_n1 := 2).
  - apply fib_2.
  - apply fib_3.
Qed.

Example fib_4_example : problem_3_spec 4 3.
Proof.
  unfold problem_3_spec.
  apply fib_step with (n := 2) (res_n := 1) (res_n1 := 2).
  - apply fib_2.
  - apply fib_3.
Qed.