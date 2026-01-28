Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_377_pre (n : nat) : Prop := True.

Definition problem_377_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

(* Helper lemmas for proving fib(14) = 377 *)
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

Lemma fib_10 : is_fib 10 55.
Proof.
  apply fib_step with (n := 8) (res_n := 21) (res_n1 := 34).
  - apply fib_8.
  - apply fib_9.
Qed.

Lemma fib_11 : is_fib 11 89.
Proof.
  apply fib_step with (n := 9) (res_n := 34) (res_n1 := 55).
  - apply fib_9.
  - apply fib_10.
Qed.

Lemma fib_12 : is_fib 12 144.
Proof.
  apply fib_step with (n := 10) (res_n := 55) (res_n1 := 89).
  - apply fib_10.
  - apply fib_11.
Qed.

Lemma fib_13 : is_fib 13 233.
Proof.
  apply fib_step with (n := 11) (res_n := 89) (res_n1 := 144).
  - apply fib_11.
  - apply fib_12.
Qed.

Lemma fib_14 : is_fib 14 377.
Proof.
  apply fib_step with (n := 12) (res_n := 144) (res_n1 := 233).
  - apply fib_12.
  - apply fib_13.
Qed.

Example fib_14_example : problem_377_spec 14 377.
Proof.
  unfold problem_377_spec.
  apply fib_step with (n := 12) (res_n := 144) (res_n1 := 233).
  - apply fib_12.
  - apply fib_13.
Qed.