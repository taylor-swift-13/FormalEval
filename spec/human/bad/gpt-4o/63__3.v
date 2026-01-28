Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Inductive is_fibfib : nat -> nat -> Prop :=
  | ff_zero : is_fibfib 0 0
  | ff_one  : is_fibfib 1 0
  | ff_two  : is_fibfib 2 1
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

Example test_case_5 : problem_63_spec 5 4.
Proof.
  eapply ff_step.
  - apply ff_two.
  - apply ff_step.
    + apply ff_one.
    + apply ff_two.
    + apply ff_step.
      * apply ff_zero.
      * apply ff_one.
      * apply ff_two.
Qed.