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

Example problem_84_test_101 :
  problem_84_spec 101 "10".
Proof.
  unfold problem_84_spec.
  exists ((101 mod 10) + ((10 mod 10) + ((1 mod 10) + 0))).
  exists "10".
  split.
  - apply sddr_base.
    eapply sddar_step with (fuel' := 100)
                           (sum_tail := (10 mod 10) + ((1 mod 10) + 0)).
    + vm_compute; reflexivity.
    + lia.
    + replace (101 / 10) with 10 by (vm_compute; reflexivity).
      eapply sddar_step with (fuel' := 99)
                             (sum_tail := (1 mod 10) + 0).
      * vm_compute; reflexivity.
      * lia.
      * replace (10 / 10) with 1 by (vm_compute; reflexivity).
        eapply sddar_step with (fuel' := 98)
                               (sum_tail := 0).
        -- vm_compute; reflexivity.
        -- lia.
        -- replace (1 / 10) with 0 by (vm_compute; reflexivity).
           apply sddar_zero.
  - split.
    + assert (Hsum :
        (101 mod 10) + ((10 mod 10) + ((1 mod 10) + 0)) = 2)
        by (vm_compute; reflexivity).
      rewrite Hsum.
      apply ntbsr_pos; [lia|].
      eapply ntbsar_even with (fuel' := 1) (n_half := 1) (s' := "1").
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * apply ntbsar_one.
    + reflexivity.
Qed.