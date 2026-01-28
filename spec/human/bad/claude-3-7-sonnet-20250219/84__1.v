Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Inductive sum_decimal_digits_aux_rel : nat -> nat -> nat -> Prop :=
  | sddar_zero : forall fuel, sum_decimal_digits_aux_rel fuel 0 0
  | sddar_zero_fuel : forall n, sum_decimal_digits_aux_rel 0 n 0
  | sddar_step : forall fuel fuel' n sum_tail,
      fuel = S fuel' ->
      n <> 0 ->
      sum_decimal_digits_aux_rel fuel' (n / 10) sum_tail ->
      sum_decimal_digits_aux_rel fuel n ((n mod 10) + sum_tail).

Inductive sum_decimal_digits_rel : nat -> nat -> Prop :=
  | sddr_base : forall n sum, sum_decimal_digits_aux_rel n n sum -> sum_decimal_digits_rel n sum.

Inductive nat_to_binary_string_pos_aux_rel : nat -> nat -> string -> Prop :=
  | ntbsar_zero_fuel : forall n, nat_to_binary_string_pos_aux_rel 0 n ""
  | ntbsar_zero_n : forall fuel, nat_to_binary_string_pos_aux_rel fuel 0 ""
  | ntbsar_one : forall fuel, nat_to_binary_string_pos_aux_rel fuel 1 "1"
  | ntbsar_even : forall fuel fuel' n n_half s',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = true ->
      n_half = n / 2 ->
      nat_to_binary_string_pos_aux_rel fuel' n_half s' ->
      nat_to_binary_string_pos_aux_rel fuel n (s' ++ "0")
  | ntbsar_odd : forall fuel fuel' n n_half s',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = false ->
      n_half = (n - 1) / 2 ->
      nat_to_binary_string_pos_aux_rel fuel' n_half s' ->
      nat_to_binary_string_pos_aux_rel fuel n (s' ++ "1").

Inductive nat_to_binary_string_rel : nat -> string -> Prop :=
  | ntbsr_zero : nat_to_binary_string_rel 0 "0"
  | ntbsr_pos : forall n s,
      n <> 0 ->
      nat_to_binary_string_pos_aux_rel n n s ->
      nat_to_binary_string_rel n s.

Definition problem_84_pre (N : nat) : Prop := (N <= 10000)%nat.

Definition problem_84_spec (N : nat) (output : string) : Prop :=
  exists sum bin_str,
    sum_decimal_digits_rel N sum /\
    nat_to_binary_string_rel sum bin_str /\
    output = bin_str.

(* Helper lemma: sum of digits of 1000 is 1, using exact fold *)
Lemma sum_decimal_digits_aux_1000 :
  sum_decimal_digits_aux_rel 4 1000 1.
Proof.
  (* unfolding the recursive calls with fuel = 4 *)
  apply sddar_step with (fuel' := 3) (sum_tail := 0).
  - reflexivity.
  - discriminate.
  - apply sddar_step with (fuel' := 2) (sum_tail := 0).
    + reflexivity.
    + discriminate.
    + apply sddar_step with (fuel' := 1) (sum_tail := 0).
      * reflexivity.
      * discriminate.
      * apply sddar_step with (fuel' := 0) (sum_tail := 0).
        { reflexivity. }
        { discriminate. }
        { apply sddar_zero_fuel. }
Qed.

Lemma sum_decimal_digits_1000 :
  sum_decimal_digits_rel 1000 1.
Proof.
  apply sddr_base.
  apply sum_decimal_digits_aux_1000.
Qed.

(* Proof that nat_to_binary_string_rel 1 "1" *)
Lemma nat_to_binary_string_rel_1 :
  nat_to_binary_string_rel 1 "1".
Proof.
  apply ntbsr_pos.
  - discriminate.
  - apply ntbsar_one.
Qed.

(* Final example: problem_84_spec for input 1000 output "1" *)
Example problem_84_example_1000 :
  problem_84_spec 1000 "1".
Proof.
  unfold problem_84_spec.
  exists 1.
  exists "1".
  repeat split.
  - apply sum_decimal_digits_1000.
  - apply nat_to_binary_string_rel_1.
  - reflexivity.
Qed.

Qed.