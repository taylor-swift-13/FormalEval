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

Example problem_84_test_1000 :
  problem_84_spec 1000 "1".
Proof.
  unfold problem_84_spec.
  (* We construct the exact sum expression corresponding to the digit-sum unfolding *)
  exists ((1000 mod 10) + ((100 mod 10) + ((10 mod 10) + ((1 mod 10) + 0)))).
  exists "1".
  split.
  - apply sddr_base.
    (* Step for n = 1000 *)
    eapply sddar_step with (fuel' := 999)
                           (sum_tail := (100 mod 10) + ((10 mod 10) + ((1 mod 10) + 0))).
    + vm_compute; reflexivity.
    + lia.
    + replace (1000 / 10) with 100 by (vm_compute; reflexivity).
      (* Step for n = 100 *)
      eapply sddar_step with (fuel' := 998)
                             (sum_tail := (10 mod 10) + ((1 mod 10) + 0)).
      * vm_compute; reflexivity.
      * lia.
      * replace (100 / 10) with 10 by (vm_compute; reflexivity).
        (* Step for n = 10 *)
        eapply sddar_step with (fuel' := 997)
                               (sum_tail := (1 mod 10) + 0).
        -- vm_compute; reflexivity.
        -- lia.
        -- replace (10 / 10) with 1 by (vm_compute; reflexivity).
           (* Step for n = 1 *)
           eapply sddar_step with (fuel' := 996)
                                  (sum_tail := 0).
           ++ vm_compute; reflexivity.
           ++ lia.
           ++ replace (1 / 10) with 0 by (vm_compute; reflexivity).
              apply sddar_zero.
  - split.
    + (* Show the binary string for the computed sum; first compute the sum to 1 *)
      assert (Hsum :
        (1000 mod 10) + ((100 mod 10) + ((10 mod 10) + ((1 mod 10) + 0))) = 1)
        by (vm_compute; reflexivity).
      rewrite Hsum.
      apply ntbsr_pos; [lia|].
      apply ntbsar_one.
    + reflexivity.
Qed.