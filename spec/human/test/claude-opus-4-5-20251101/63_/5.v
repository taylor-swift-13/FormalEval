Require Import Coq.Init.Nat.

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

Example test_fibfib_10 : problem_63_spec 10 81.
Proof.
  unfold problem_63_spec.
  assert (H0: is_fibfib 0 0) by apply ff_zero.
  assert (H1: is_fibfib 1 0) by apply ff_one.
  assert (H2: is_fibfib 2 1) by apply ff_two.
  assert (H3: is_fibfib 3 1) by (apply (ff_step 0 0 0 1); assumption).
  assert (H4: is_fibfib 4 2) by (apply (ff_step 1 0 1 1); assumption).
  assert (H5: is_fibfib 5 4) by (apply (ff_step 2 1 1 2); assumption).
  assert (H6: is_fibfib 6 7) by (apply (ff_step 3 1 2 4); assumption).
  assert (H7: is_fibfib 7 13) by (apply (ff_step 4 2 4 7); assumption).
  assert (H8: is_fibfib 8 24) by (apply (ff_step 5 4 7 13); assumption).
  assert (H9: is_fibfib 9 44) by (apply (ff_step 6 7 13 24); assumption).
  assert (H10: is_fibfib 10 81) by (apply (ff_step 7 13 24 44); assumption).
  exact H10.
Qed.