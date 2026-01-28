Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.
Open Scope nat_scope.

Fixpoint sum_decimal_digits_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_decimal_digits_aux f' (n / 10)
    end
  end.

Definition sum_decimal_digits (n : nat) : nat :=
  sum_decimal_digits_aux n n.

Fixpoint nat_to_binary_string_pos_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => ""
  | S f' =>
      if Nat.eqb n 0 then ""
      else nat_to_binary_string_pos_aux f' (n / 2) ++ (if Nat.eqb (n mod 2) 0 then "0" else "1")
  end.

Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else nat_to_binary_string_pos_aux n n.

Definition solve_impl (N : nat) : string :=
  nat_to_binary_string (sum_decimal_digits N).

Definition problem_84_pre (N : nat) : Prop := (N <= 10000)%nat.

Definition problem_84_spec (N : nat) (output : string) : Prop :=
  output = solve_impl N.

Example problem_84_test_case_1 :
  problem_84_spec 70 "111".
Proof.
  unfold problem_84_spec, solve_impl.
  simpl.
  unfold sum_decimal_digits.
  simpl sum_decimal_digits_aux.
  unfold nat_to_binary_string.
  simpl nat_to_binary_string_pos_aux.
  reflexivity.
Qed.