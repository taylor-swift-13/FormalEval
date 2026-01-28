(* 导入Coq中处理字符串和列表所需的基础库 *)
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

Example test_problem_79 : problem_79_spec 259 "db100000011db".
Proof.
  unfold problem_79_spec.
  exists "100000011".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + apply (ntbsar_odd 259 258 259 129 "10000001") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 258 257 129 64 "1000000") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 257 256 64 32 "100000") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 256 255 32 16 "10000") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 255 254 16 8 "1000") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 254 253 8 4 "100") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 253 252 4 2 "10") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 252 251 2 1 "1") ; try reflexivity ; try discriminate.
      apply ntbsar_one.
  - reflexivity.
Qed.