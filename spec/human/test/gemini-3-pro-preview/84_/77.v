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

Example test_case_4998: problem_84_spec 4998 "11110".
Proof.
  exists 30, "11110".
  split.
  - apply sddr_base.
    assert (H1: 30 = (4998 mod 10) + 22). { vm_compute. reflexivity. }
    rewrite H1.
    apply sddar_step with (fuel' := 4997).
    + reflexivity.
    + lia.
    + assert (H1_div: 4998 / 10 = 499). { vm_compute. reflexivity. }
      rewrite H1_div.
      assert (H2: 22 = (499 mod 10) + 13). { vm_compute. reflexivity. }
      rewrite H2.
      apply sddar_step with (fuel' := 4996).
      * reflexivity.
      * lia.
      * assert (H2_div: 499 / 10 = 49). { vm_compute. reflexivity. }
        rewrite H2_div.
        assert (H3: 13 = (49 mod 10) + 4). { vm_compute. reflexivity. }
        rewrite H3.
        apply sddar_step with (fuel' := 4995).
        -- reflexivity.
        -- lia.
        -- assert (H3_div: 49 / 10 = 4). { vm_compute. reflexivity. }
           rewrite H3_div.
           assert (H4: 4 = (4 mod 10) + 0). { vm_compute. reflexivity. }
           rewrite H4.
           apply sddar_step with (fuel' := 4994).
           ++ reflexivity.
           ++ lia.
           ++ assert (H4_div: 4 / 10 = 0). { vm_compute. reflexivity. }
              rewrite H4_div.
              apply sddar_zero.
  - split.
    + apply ntbsr_pos.
      * lia.
      * apply ntbsar_even with (fuel' := 29) (n_half := 15) (s' := "1111").
        -- reflexivity.
        -- lia.
        -- lia.
        -- reflexivity.
        -- reflexivity.
        -- apply ntbsar_odd with (fuel' := 28) (n_half := 7) (s' := "111").
           ++ reflexivity.
           ++ lia.
           ++ lia.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply ntbsar_odd with (fuel' := 27) (n_half := 3) (s' := "11").
              ** reflexivity.
              ** lia.
              ** lia.
              ** reflexivity.
              ** reflexivity.
              ** apply ntbsar_odd with (fuel' := 26) (n_half := 1) (s' := "1").
                 --- reflexivity.
                 --- lia.
                 --- lia.
                 --- reflexivity.
                 --- reflexivity.
                 --- apply ntbsar_one.
    + reflexivity.
Qed.