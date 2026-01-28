Require Import Coq.Init.Nat.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

Example problem_55_test_6 : problem_55_pre 6 /\ problem_55_spec 6 8.
Proof.
  split; [exact I|].
  pose proof fib_zero as H0.
  pose proof fib_one as H1.
  pose proof (fib_step 0 0 1 H0 H1) as H2.
  pose proof (fib_step 1 1 1 H1 H2) as H3.
  pose proof (fib_step 2 1 2 H2 H3) as H4.
  pose proof (fib_step 3 2 3 H3 H4) as H5.
  pose proof (fib_step 4 3 5 H4 H5) as H6.
  exact H6.
Qed.