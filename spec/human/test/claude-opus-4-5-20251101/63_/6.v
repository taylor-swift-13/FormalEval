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

Example test_fibfib_12 : problem_63_spec 12 274.
Proof.
  unfold problem_63_spec.
  assert (H0: is_fibfib 0 0) by apply ff_zero.
  assert (H1: is_fibfib 1 0) by apply ff_one.
  assert (H2: is_fibfib 2 1) by apply ff_two.
  assert (H3: is_fibfib 3 1) by (apply (ff_step 0 0 0 1 H0 H1 H2)).
  assert (H4: is_fibfib 4 2) by (apply (ff_step 1 0 1 1 H1 H2 H3)).
  assert (H5: is_fibfib 5 4) by (apply (ff_step 2 1 1 2 H2 H3 H4)).
  assert (H6: is_fibfib 6 7) by (apply (ff_step 3 1 2 4 H3 H4 H5)).
  assert (H7: is_fibfib 7 13) by (apply (ff_step 4 2 4 7 H4 H5 H6)).
  assert (H8: is_fibfib 8 24) by (apply (ff_step 5 4 7 13 H5 H6 H7)).
  assert (H9: is_fibfib 9 44) by (apply (ff_step 6 7 13 24 H6 H7 H8)).
  assert (H10: is_fibfib 10 81) by (apply (ff_step 7 13 24 44 H7 H8 H9)).
  assert (H11: is_fibfib 11 149) by (apply (ff_step 8 24 44 81 H8 H9 H10)).
  assert (H12: is_fibfib 12 274) by (apply (ff_step 9 44 81 149 H9 H10 H11)).
  exact H12.
Qed.