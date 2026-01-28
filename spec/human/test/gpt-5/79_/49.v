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

Example problem_79_pre_test_0 : problem_79_pre 45.
Proof.
  unfold problem_79_pre.
  exact I.
Qed.

Example problem_79_spec_test_0 : problem_79_spec 45 "db101101db".
Proof.
  unfold problem_79_spec.
  exists "101101".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + assert (H1 : nat_to_binary_string_aux_rel 1 40 "1").
      { apply ntbsar_one. }
      assert (H2 : nat_to_binary_string_aux_rel 2 41 "10").
      { eapply ntbsar_even with (fuel' := 40) (n := 2) (n_half := 1) (s' := "1").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H1.
      }
      assert (H3 : nat_to_binary_string_aux_rel 5 42 "101").
      { eapply ntbsar_odd with (fuel' := 41) (n := 5) (n_half := 2) (s' := "10").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H2.
      }
      assert (H4 : nat_to_binary_string_aux_rel 11 43 "1011").
      { eapply ntbsar_odd with (fuel' := 42) (n := 11) (n_half := 5) (s' := "101").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H3.
      }
      assert (H5 : nat_to_binary_string_aux_rel 22 44 "10110").
      { eapply ntbsar_even with (fuel' := 43) (n := 22) (n_half := 11) (s' := "1011").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H4.
      }
      eapply ntbsar_odd with (fuel' := 44) (n := 45) (n_half := 22) (s' := "10110").
      * reflexivity.
      * discriminate.
      * discriminate.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * exact H5.
  - simpl. reflexivity.
Qed.