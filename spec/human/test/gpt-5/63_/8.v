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

Example fibfib_12_example : is_fibfib 12 274.
Proof.
  apply (ff_step 9 44 81 149).
  - apply fibfib_9_example.
  - apply fibfib_10_example.
  - apply fibfib_11_example.
Qed.

Example fibfib_13_example : is_fibfib 13 504.
Proof.
  apply (ff_step 10 81 149 274).
  - apply fibfib_10_example.
  - apply fibfib_11_example.
  - apply fibfib_12_example.
Qed.

Example fibfib_14_example : is_fibfib 14 927.
Proof.
  apply (ff_step 11 149 274 504).
  - apply fibfib_11_example.
  - apply fibfib_12_example.
  - apply fibfib_13_example.
Qed.

Example fibfib_15_example : is_fibfib 15 1705.
Proof.
  apply (ff_step 12 274 504 927).
  - apply fibfib_12_example.
  - apply fibfib_13_example.
  - apply fibfib_14_example.
Qed.

Example fibfib_16_example : is_fibfib 16 3136.
Proof.
  apply (ff_step 13 504 927 1705).
  - apply fibfib_13_example.
  - apply fibfib_14_example.
  - apply fibfib_15_example.
Qed.

Example fibfib_17_example : is_fibfib 17 5768.
Proof.
  apply (ff_step 14 927 1705 3136).
  - apply fibfib_14_example.
  - apply fibfib_15_example.
  - apply fibfib_16_example.
Qed.

Example fibfib_18_example : is_fibfib 18 10609.
Proof.
  apply (ff_step 15 1705 3136 5768).
  - apply fibfib_15_example.
  - apply fibfib_16_example.
  - apply fibfib_17_example.
Qed.

Example fibfib_19_example : is_fibfib 19 19513.
Proof.
  apply (ff_step 16 3136 5768 10609).
  - apply fibfib_16_example.
  - apply fibfib_17_example.
  - apply fibfib_18_example.
Qed.

Example fibfib_20_example : is_fibfib 20 35890.
Proof.
  apply (ff_step 17 5768 10609 19513).
  - apply fibfib_17_example.
  - apply fibfib_18_example.
  - apply fibfib_19_example.
Qed.

Example test_case_problem_63_nat :
  problem_63_spec 20 35890.
Proof.
  unfold problem_63_spec.
  apply fibfib_20_example.
Qed.

Example test_case_problem_63_Z :
  problem_63_spec (Z.to_nat 20%Z) (Z.to_nat 35890%Z).
Proof.
  change (problem_63_spec 20 35890).
  unfold problem_63_spec.
  apply fibfib_20_example.
Qed.