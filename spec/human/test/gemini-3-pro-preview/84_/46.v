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

Example test_case_97: problem_84_spec 97 "10000".
Proof.
  exists 16, "10000".
  split.
  - apply sddr_base.
    (* Step 1: 97 -> 9 *)
    assert (H1: 16 = (97 mod 10) + 9). { vm_compute. reflexivity. }
    rewrite H1.
    apply sddar_step with (fuel' := 96).
    + lia.
    + lia.
    + assert (H1_div: 97 / 10 = 9). { vm_compute. reflexivity. }
      rewrite H1_div.
      (* Step 2: 9 -> 0 *)
      assert (H2: 9 = (9 mod 10) + 0). { vm_compute. reflexivity. }
      rewrite H2.
      apply sddar_step with (fuel' := 95).
      * lia.
      * lia.
      * assert (H2_div: 9 / 10 = 0). { vm_compute. reflexivity. }
        rewrite H2_div.
        apply sddar_zero.
  - split.
    + apply ntbsr_pos.
      * lia.
      * apply ntbsar_even with (fuel' := 15) (n_half := 8) (s' := "1000").
        -- lia.
        -- lia.
        -- lia.
        -- reflexivity.
        -- reflexivity.
        -- apply ntbsar_even with (fuel' := 14) (n_half := 4) (s' := "100").
           ++ lia.
           ++ lia.
           ++ lia.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply ntbsar_even with (fuel' := 13) (n_half := 2) (s' := "10").
              ** lia.
              ** lia.
              ** lia.
              ** reflexivity.
              ** reflexivity.
              ** apply ntbsar_even with (fuel' := 12) (n_half := 1) (s' := "1").
                 --- lia.
                 --- lia.
                 --- lia.
                 --- reflexivity.
                 --- reflexivity.
                 --- apply ntbsar_one.
    + reflexivity.
Qed.