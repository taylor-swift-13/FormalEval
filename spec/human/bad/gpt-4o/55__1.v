(* Import the standard library for natural numbers *)
Require Import Coq.Init.Nat.

(* Inductive definition for the Fibonacci relation *)
Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

(* Specification for the Fibonacci function *)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

(* Helper lemma for fib(2) = 1 *)
Lemma fib_2 : is_fib 2 1.
Proof.
  apply fib_step with (res_n := 1) (res_n1 := 1).
  - apply fib_one.
  - apply fib_one.
Qed.

(* Helper lemma for fib(3) = 2 *)
Lemma fib_3 : is_fib 3 2.
Proof.
  apply fib_step with (res_n := 1) (res_n1 := 1).
  - apply fib_one.
  - apply fib_2.
Qed.

(* Helper lemma for fib(4) = 3 *)
Lemma fib_4 : is_fib 4 3.
Proof.
  apply fib_step with (res_n := 2) (res_n1 := 1).
  - apply fib_3.
  - apply fib_2.
Qed.

(* Helper lemma for fib(5) = 5 *)
Lemma fib_5 : is_fib 5 5.
Proof.
  apply fib_step with (res_n := 3) (res_n1 := 2).
  - apply fib_4.
  - apply fib_3.
Qed.

(* Helper lemma for fib(6) = 8 *)
Lemma fib_6 : is_fib 6 8.
Proof.
  apply fib_step with (res_n := 5) (res_n1 := 3).
  - apply fib_5.
  - apply fib_4.
Qed.

(* Helper lemma for fib(7) = 13 *)
Lemma fib_7 : is_fib 7 13.
Proof.
  apply fib_step with (res_n := 8) (res_n1 := 5).
  - apply fib_6.
  - apply fib_5.
Qed.

(* Helper lemma for fib(8) = 21 *)
Lemma fib_8 : is_fib 8 21.
Proof.
  apply fib_step with (res_n := 13) (res_n1 := 8).
  - apply fib_7.
  - apply fib_6.
Qed.

(* Helper lemma for fib(9) = 34 *)
Lemma fib_9 : is_fib 9 34.
Proof.
  apply fib_step with (res_n := 21) (res_n1 := 13).
  - apply fib_8.
  - apply fib_7.
Qed.

(* Example proof for the test case fib(10) = 55 *)
Example test_fib_10 : problem_55_spec 10 55.
Proof.
  apply fib_step with (res_n := 34) (res_n1 := 21).
  - apply fib_9.
  - apply fib_8.
Qed.