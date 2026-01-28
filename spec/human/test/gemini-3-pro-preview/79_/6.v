Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

(* Definition of the relation as provided in the specification *)
Inductive nat_to_binary_string_aux_rel : nat -> nat -> string -> Prop :=
  | ntbsar_zero_fuel : forall n, nat_to_binary_string_aux_rel n 0 ""
  | ntbsar_zero_n : forall fuel, nat_to_binary_string_aux_rel 0 (S fuel) "0"
  | ntbsar_one : forall fuel, nat_to_binary_string_aux_rel 1 (S fuel) "1"
  | ntbsar_even : forall fuel fuel' n n_half s',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = true ->
      n_half = n / 2 ->
      nat_to_binary_string_aux_rel n_half fuel' s' ->
      nat_to_binary_string_aux_rel n fuel (s' ++ "0")
  | ntbsar_odd : forall fuel fuel' n n_half s',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = false ->
      n_half = (n - 1) / 2 ->
      nat_to_binary_string_aux_rel n_half fuel' s' ->
      nat_to_binary_string_aux_rel n fuel (s' ++ "1").

Inductive nat_to_binary_string_rel : nat -> string -> Prop :=
  | ntbsr_zero : nat_to_binary_string_rel 0 "0"
  | ntbsr_pos : forall n s,
      n <> 0 ->
      nat_to_binary_string_aux_rel n n s ->
      nat_to_binary_string_rel n s.

Definition problem_79_pre (decimal : nat) : Prop := True.

Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  exists s,
    nat_to_binary_string_rel decimal s /\
    output = "db" ++ s ++ "db".

(* Proof for the test case input = 255, output = "db11111111db" *)
Example test_case_1 : problem_79_spec 255 "db11111111db".
Proof.
  unfold problem_79_spec.
  exists "11111111".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + change "11111111" with ("1111111" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      change "1111111" with ("111111" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      change "111111" with ("11111" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      change "11111" with ("1111" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      change "1111" with ("111" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      change "111" with ("11" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      change "11" with ("1" ++ "1").
      eapply ntbsar_odd; try reflexivity; try discriminate.
      apply ntbsar_one.
  - simpl. reflexivity.
Qed.