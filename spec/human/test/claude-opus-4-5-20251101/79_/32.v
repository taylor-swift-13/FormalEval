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

Example test_problem_79 : problem_79_spec 1021 "db1111111101db".
Proof.
  unfold problem_79_spec.
  exists "1111111101".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + apply (ntbsar_odd 1021 1020 1021 510 "111111110") ; try reflexivity ; try discriminate.
      apply (ntbsar_even 1020 1019 510 255 "11111111") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1019 1018 255 127 "1111111") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1018 1017 127 63 "111111") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1017 1016 63 31 "11111") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1016 1015 31 15 "1111") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1015 1014 15 7 "111") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1014 1013 7 3 "11") ; try reflexivity ; try discriminate.
      apply (ntbsar_odd 1013 1012 3 1 "1") ; try reflexivity ; try discriminate.
      apply ntbsar_one.
  - reflexivity.
Qed.