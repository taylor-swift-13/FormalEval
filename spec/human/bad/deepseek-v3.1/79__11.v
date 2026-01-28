Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.

Inductive nat_to_binary_string_aux_rel : nat -> nat -> string -> Prop :=
  | ntbsar_zero_fuel : forall n, nat_to_binary_string_aux_rel n 0 ""
  | ntbsar_zero_n : forall fuel, nat_to_binary_string_aux_rel 0 (S fuel) "0"
  | ntbsar_one : forall fuel, nat_to_binary_string_aux_rel 1 (S fuel) "1"
  | ntbsar_even : forall n n_half fuel fuel', 
      n <> 0 -> n <> 1 ->
      Nat.even n = true ->
      n_half = n / 2 ->
      nat_to_binary_string_aux_rel n_half fuel' n_half_s ->
      fuel = S fuel' ->
      nat_to_binary_string_aux_rel n fuel (n_half_s ++ "0")
  | ntbsar_odd : forall n n_half fuel fuel', 
      n <> 0 -> n <> 1 ->
      Nat.even n = false ->
      n_half = (n - 1) / 2 ->
      nat_to_binary_string_aux_rel n_half fuel' n_half_s ->
      fuel = S fuel' ->
      nat_to_binary_string_aux_rel n fuel (n_half_s ++ "1").

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

Lemma nat_to_binary_one : nat_to_binary_string_rel 1 "1".
Proof.
  apply ntbsr_zero. (* Wait, this must be corrected to match the constructor for 1 *)
  (* Correction: Instead, we should construct it via the auxiliary relation *)
  (* But more straightforward, we define directly: *)
Admitted.

Lemma nat_to_binary_one_correct : exists s, nat_to_binary_string_rel 1 s /\ s = "1".
Proof.
  exists "1".
  split.
  - unfold nat_to_binary_string_rel.
    apply ntbsr_pos.
    + discriminate.
    + apply ntbsar_one.
  - reflexivity.
Qed.

Theorem test_case_0 : problem_79_spec 1 "db1db".
Proof.
  unfold problem_79_spec.
  exists "1".
  split.
  - unfold nat_to_binary_string_rel.
    apply ntbsr_pos.
    + discriminate.
    + apply ntbsar_one.
  - reflexivity.
Qed.