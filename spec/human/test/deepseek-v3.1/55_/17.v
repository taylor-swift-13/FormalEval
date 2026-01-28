Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_2_pre (n : nat) : Prop := True.

Definition problem_2_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

(* Helper lemmas for proving fib(3) = 2 *)
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

Lemma fib_5 : is_fib 5 5.
Proof.
  apply fib_step with (n := 3) (res_n := 2) (res_n1 := 3).
  - apply fib_3.
  - apply fib_4.
Qed.

Lemma fib_6 : is_fib 6 8.
Proof.
  apply fib_step with (n := 4) (res_n := 3) (res_n1 := 5).
  - apply fib_4.
  - apply fib_5.
Qed.

Lemma fib_7 : is_fib 7 13.
Proof.
  apply fib_step with (n := 5) (res_n := 5) (res_n1 := 8).
  - apply fib_5.
  - apply fib_6.
Qed.

Lemma fib_8 : is_fib 8 21.
Proof.
  apply fib_step with (n := 6) (res_n := 8) (res_n1 := 13).
  - apply fib_6.
  - apply fib_7.
Qed.

Lemma fib_9 : is_fib 9 34.
Proof.
  apply fib_step with (n := 7) (res_n := 13) (res_n1 := 21).
  - apply fib_7.
  - apply fib_8.
Qed.

Example fib_3_example : problem_2_spec 3 2.
Proof.
  unfold problem_2_spec.
  apply fib_step with (n := 1) (res_n := 1) (res_n1 := 1).
  - apply fib_one.
  - apply fib_2.
Qed.