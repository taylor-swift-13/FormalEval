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

Example problem_55_test_27 : problem_55_pre 27 /\ problem_55_spec 27 196418.
Proof.
  split; [exact I|].
  pose proof fib_zero as H0.
  pose proof fib_one as H1.
  pose proof (fib_step 0 0 1 H0 H1) as H2.
  pose proof (fib_step 1 1 1 H1 H2) as H3.
  pose proof (fib_step 2 1 2 H2 H3) as H4.
  pose proof (fib_step 3 2 3 H3 H4) as H5.
  pose proof (fib_step 4 3 5 H4 H5) as H6.
  pose proof (fib_step 5 5 8 H5 H6) as H7.
  pose proof (fib_step 6 8 13 H6 H7) as H8.
  pose proof (fib_step 7 13 21 H7 H8) as H9.
  pose proof (fib_step 8 21 34 H8 H9) as H10.
  pose proof (fib_step 9 34 55 H9 H10) as H11.
  pose proof (fib_step 10 55 89 H10 H11) as H12.
  pose proof (fib_step 11 89 144 H11 H12) as H13.
  pose proof (fib_step 12 144 233 H12 H13) as H14.
  pose proof (fib_step 13 233 377 H13 H14) as H15.
  pose proof (fib_step 14 377 610 H14 H15) as H16.
  pose proof (fib_step 15 610 987 H15 H16) as H17.
  pose proof (fib_step 16 987 1597 H16 H17) as H18.
  pose proof (fib_step 17 1597 2584 H17 H18) as H19.
  pose proof (fib_step 18 2584 4181 H18 H19) as H20.
  pose proof (fib_step 19 4181 6765 H19 H20) as H21.
  pose proof (fib_step 20 6765 10946 H20 H21) as H22.
  pose proof (fib_step 21 10946 17711 H21 H22) as H23.
  pose proof (fib_step 22 17711 28657 H22 H23) as H24.
  pose proof (fib_step 23 28657 46368 H23 H24) as H25.
  pose proof (fib_step 24 46368 75025 H24 H25) as H26.
  pose proof (fib_step 25 75025 121393 H25 H26) as H27.
  exact H27.
Qed.