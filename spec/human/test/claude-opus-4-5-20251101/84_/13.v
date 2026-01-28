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

Example test_problem_84 : problem_84_spec 15 "110".
Proof.
  unfold problem_84_spec.
  exists 6, "110".
  split; [| split].
  - apply sddr_base.
    assert (H15mod: 15 mod 10 = 5) by reflexivity.
    assert (H15div: 15 / 10 = 1) by reflexivity.
    assert (H1mod: 1 mod 10 = 1) by reflexivity.
    assert (H1div: 1 / 10 = 0) by reflexivity.
    apply (sddar_step 15 14 15 1).
    + reflexivity.
    + lia.
    + rewrite H15div.
      apply (sddar_step 14 13 1 0).
      * reflexivity.
      * lia.
      * rewrite H1div.
        apply sddar_zero.
  - apply ntbsr_pos.
    + lia.
    + assert (H6even: Nat.even 6 = true) by reflexivity.
      assert (H6div: 6 / 2 = 3) by reflexivity.
      assert (H3even: Nat.even 3 = false) by reflexivity.
      assert (H3sub: (3 - 1) / 2 = 1) by reflexivity.
      apply (ntbsar_even 6 5 6 3 "11").
      * reflexivity.
      * lia.
      * lia.
      * exact H6even.
      * exact H6div.
      * apply (ntbsar_odd 5 4 3 1 "1").
        -- reflexivity.
        -- lia.
        -- lia.
        -- exact H3even.
        -- exact H3sub.
        -- apply ntbsar_one.
  - reflexivity.
Qed.