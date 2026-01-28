Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

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

Example fibfib_3_example : is_fibfib 3 1.
Proof.
  apply (ff_step 0 0 0 1).
  - apply ff_zero.
  - apply ff_one.
  - apply ff_two.
Qed.

Example fibfib_4_example : is_fibfib 4 2.
Proof.
  apply (ff_step 1 0 1 1).
  - apply ff_one.
  - apply ff_two.
  - apply fibfib_3_example.
Qed.

Example fibfib_5_example : is_fibfib 5 4.
Proof.
  apply (ff_step 2 1 1 2).
  - apply ff_two.
  - apply fibfib_3_example.
  - apply fibfib_4_example.
Qed.

Example fibfib_6_example : is_fibfib 6 7.
Proof.
  apply (ff_step 3 1 2 4).
  - apply fibfib_3_example.
  - apply fibfib_4_example.
  - apply fibfib_5_example.
Qed.

Example fibfib_7_example : is_fibfib 7 13.
Proof.
  apply (ff_step 4 2 4 7).
  - apply fibfib_4_example.
  - apply fibfib_5_example.
  - apply fibfib_6_example.
Qed.

Example fibfib_8_example : is_fibfib 8 24.
Proof.
  apply (ff_step 5 4 7 13).
  - apply fibfib_5_example.
  - apply fibfib_6_example.
  - apply fibfib_7_example.
Qed.

Example fibfib_9_example : is_fibfib 9 44.
Proof.
  apply (ff_step 6 7 13 24).
  - apply fibfib_6_example.
  - apply fibfib_7_example.
  - apply fibfib_8_example.
Qed.

Example fibfib_10_example : is_fibfib 10 81.
Proof.
  apply (ff_step 7 13 24 44).
  - apply fibfib_7_example.
  - apply fibfib_8_example.
  - apply fibfib_9_example.
Qed.

Example fibfib_11_example : is_fibfib 11 149.
Proof.
  apply (ff_step 8 24 44 81).
  - apply fibfib_8_example.
  - apply fibfib_9_example.
  - apply fibfib_10_example.
Qed.

Example test_case_problem_63_nat :
  problem_63_spec 11 149.
Proof.
  unfold problem_63_spec.
  apply fibfib_11_example.
Qed.

Example test_case_problem_63_Z :
  problem_63_spec (Z.to_nat 11%Z) (Z.to_nat 149%Z).
Proof.
  change (problem_63_spec 11 149).
  unfold problem_63_spec.
  apply fibfib_11_example.
Qed.