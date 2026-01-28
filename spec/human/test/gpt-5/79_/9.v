Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

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

Example problem_79_pre_test_0 : problem_79_pre 7.
Proof.
  unfold problem_79_pre.
  exact I.
Qed.

Example problem_79_spec_test_0 : problem_79_spec 7 "db111db".
Proof.
  unfold problem_79_spec.
  exists "111".
  split.
  - apply ntbsr_pos with (n := 7).
    + intro H. discriminate.
    + eapply ntbsar_odd with (fuel' := 6) (n := 7) (n_half := 3) (s' := "11").
      * reflexivity.
      * intro H. discriminate.
      * intro H. discriminate.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * eapply ntbsar_odd with (fuel' := 5) (n := 3) (n_half := 1) (s' := "1").
        -- reflexivity.
        -- intro H. discriminate.
        -- intro H. discriminate.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- apply ntbsar_one.
  - simpl. reflexivity.
Qed.