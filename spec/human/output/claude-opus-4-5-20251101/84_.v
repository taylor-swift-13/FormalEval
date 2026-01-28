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

Example test_problem_84 : problem_84_spec 1000 "1".
Proof.
  unfold problem_84_spec.
  exists 1, "1".
  split; [| split].
  - (* sum_decimal_digits_rel 1000 1 *)
    apply sddr_base.
    (* We need to show sum_decimal_digits_aux_rel 1000 1000 1 *)
    (* 1000 mod 10 = 0, 1000 / 10 = 100 *)
    (* 100 mod 10 = 0, 100 / 10 = 10 *)
    (* 10 mod 10 = 0, 10 / 10 = 1 *)
    (* 1 mod 10 = 1, 1 / 10 = 0 *)
    (* sum = 0 + 0 + 0 + 1 = 1 *)
    assert (H1: (1000 mod 10 + (100 mod 10 + (10 mod 10 + (1 mod 10 + 0)))) = 1) by reflexivity.
    apply (sddar_step 1000 999 1000 (100 mod 10 + (10 mod 10 + (1 mod 10 + 0)))).
    + reflexivity.
    + lia.
    + apply (sddar_step 999 998 100 (10 mod 10 + (1 mod 10 + 0))).
      * reflexivity.
      * lia.
      * apply (sddar_step 998 997 10 (1 mod 10 + 0)).
        -- reflexivity.
        -- lia.
        -- assert (H2: 10 / 10 = 1) by reflexivity.
           rewrite H2.
           apply (sddar_step 997 996 1 0).
           ++ reflexivity.
           ++ lia.
           ++ assert (H3: 1 / 10 = 0) by reflexivity.
              rewrite H3.
              apply sddar_zero.
  - (* nat_to_binary_string_rel 1 "1" *)
    apply ntbsr_pos.
    + lia.
    + apply ntbsar_one.
  - reflexivity.
Qed.