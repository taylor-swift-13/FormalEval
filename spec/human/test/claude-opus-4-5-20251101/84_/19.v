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

Example test_problem_84 : problem_84_spec 17 "1000".
Proof.
  unfold problem_84_spec.
  exists 8, "1000".
  split; [| split].
  - apply sddr_base.
    assert (H17mod: 17 mod 10 = 7) by reflexivity.
    assert (H17div: 17 / 10 = 1) by reflexivity.
    assert (H1mod: 1 mod 10 = 1) by reflexivity.
    assert (H1div: 1 / 10 = 0) by reflexivity.
    apply (sddar_step 17 16 17 1).
    + reflexivity.
    + lia.
    + rewrite H17div.
      apply (sddar_step 16 15 1 0).
      * reflexivity.
      * lia.
      * rewrite H1div.
        apply sddar_zero.
  - apply ntbsr_pos.
    + lia.
    + assert (H8even: Nat.even 8 = true) by reflexivity.
      assert (H8div: 8 / 2 = 4) by reflexivity.
      assert (H4even: Nat.even 4 = true) by reflexivity.
      assert (H4div: 4 / 2 = 2) by reflexivity.
      assert (H2even: Nat.even 2 = true) by reflexivity.
      assert (H2div: 2 / 2 = 1) by reflexivity.
      apply (ntbsar_even 8 7 8 4 "100").
      * reflexivity.
      * lia.
      * lia.
      * exact H8even.
      * exact H8div.
      * apply (ntbsar_even 7 6 4 2 "10").
        -- reflexivity.
        -- lia.
        -- lia.
        -- exact H4even.
        -- exact H4div.
        -- apply (ntbsar_even 6 5 2 1 "1").
           ++ reflexivity.
           ++ lia.
           ++ lia.
           ++ exact H2even.
           ++ exact H2div.
           ++ apply ntbsar_one.
  - reflexivity.
Qed.