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

Example test_case_9999: problem_84_spec 9999 "100100".
Proof.
  exists 36, "100100".
  split.
  - apply sddr_base.
    (* Step 1: 9999 -> 999 *)
    replace 36 with ((9999 mod 10) + 27) by (vm_compute; reflexivity).
    apply sddar_step with (fuel' := 9998).
    + vm_compute; reflexivity.
    + vm_compute; discriminate.
    + replace (9999 / 10) with 999 by (vm_compute; reflexivity).
      (* Step 2: 999 -> 99 *)
      replace 27 with ((999 mod 10) + 18) by (vm_compute; reflexivity).
      apply sddar_step with (fuel' := 9997).
      * vm_compute; reflexivity.
      * vm_compute; discriminate.
      * replace (999 / 10) with 99 by (vm_compute; reflexivity).
        (* Step 3: 99 -> 9 *)
        replace 18 with ((99 mod 10) + 9) by (vm_compute; reflexivity).
        apply sddar_step with (fuel' := 9996).
        -- vm_compute; reflexivity.
        -- vm_compute; discriminate.
        -- replace (99 / 10) with 9 by (vm_compute; reflexivity).
           (* Step 4: 9 -> 0 *)
           replace 9 with ((9 mod 10) + 0) by (vm_compute; reflexivity).
           apply sddar_step with (fuel' := 9995).
           ++ vm_compute; reflexivity.
           ++ vm_compute; discriminate.
           ++ replace (9 / 10) with 0 by (vm_compute; reflexivity).
              apply sddar_zero.
  - split.
    + apply ntbsr_pos.
      * vm_compute; discriminate.
      * (* 36 -> "100100" *)
        apply ntbsar_even with (fuel' := 35) (n_half := 18) (s' := "10010").
        -- reflexivity.
        -- vm_compute; discriminate.
        -- vm_compute; discriminate.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- (* 18 -> "10010" *)
           apply ntbsar_even with (fuel' := 34) (n_half := 9) (s' := "1001").
           ++ reflexivity.
           ++ vm_compute; discriminate.
           ++ vm_compute; discriminate.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ (* 9 -> "1001" *)
              apply ntbsar_odd with (fuel' := 33) (n_half := 4) (s' := "100").
              ** reflexivity.
              ** vm_compute; discriminate.
              ** vm_compute; discriminate.
              ** vm_compute; reflexivity.
              ** vm_compute; reflexivity.
              ** (* 4 -> "100" *)
                 apply ntbsar_even with (fuel' := 32) (n_half := 2) (s' := "10").
                 --- reflexivity.
                 --- vm_compute; discriminate.
                 --- vm_compute; discriminate.
                 --- vm_compute; reflexivity.
                 --- vm_compute; reflexivity.
                 --- (* 2 -> "10" *)
                     apply ntbsar_even with (fuel' := 31) (n_half := 1) (s' := "1").
                     +++ reflexivity.
                     +++ vm_compute; discriminate.
                     +++ vm_compute; discriminate.
                     +++ vm_compute; reflexivity.
                     +++ vm_compute; reflexivity.
                     +++ apply ntbsar_one.
    + reflexivity.
Qed.