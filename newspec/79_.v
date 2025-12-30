(* def decimal_to_binary(decimal):
"""You will be given a number in decimal form and your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' or '1'.

There will be an extra couple of characters 'db' at the beginning and at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15) # returns "db1111db"
decimal_to_binary(32) # returns "db100000db"
""" *)
(* 导入Coq中处理字符串和列表所需的基础库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Inductive nat_to_binary_list_aux_rel : nat -> nat -> list bool -> Prop :=
  | ntblar_zero_fuel : forall n, nat_to_binary_list_aux_rel n 0 []
  | ntblar_zero_n : forall fuel, nat_to_binary_list_aux_rel 0 fuel [false]
  | ntblar_one : forall fuel, nat_to_binary_list_aux_rel 1 fuel [true]
  | ntblar_even : forall fuel fuel' n n_half bl',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = true ->
      n_half = n / 2 ->
      nat_to_binary_list_aux_rel n_half fuel' bl' ->
      nat_to_binary_list_aux_rel n fuel (bl' ++ [false])
  | ntblar_odd : forall fuel fuel' n n_half bl',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = false ->
      n_half = (n - 1) / 2 ->
      nat_to_binary_list_aux_rel n_half fuel' bl' ->
      nat_to_binary_list_aux_rel n fuel (bl' ++ [true]).

Inductive nat_to_binary_list_rel : nat -> list bool -> Prop :=
  | ntblr_zero : nat_to_binary_list_rel 0 [false]
  | ntblr_pos : forall n bl,
      n <> 0 ->
      nat_to_binary_list_aux_rel n n bl ->
      nat_to_binary_list_rel n bl.

Inductive binary_list_to_string_rel : list bool -> string -> Prop :=
  | bltsr_nil : binary_list_to_string_rel [] ""
  | bltsr_true : forall b tl s',
      b = true ->
      binary_list_to_string_rel tl s' ->
      binary_list_to_string_rel (b :: tl) ("1" ++ s')
  | bltsr_false : forall b tl s',
      b = false ->
      binary_list_to_string_rel tl s' ->
      binary_list_to_string_rel (b :: tl) ("0" ++ s').


Definition problem_79_pre (decimal : nat) : Prop := True.

Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  exists bl bl_str,
    nat_to_binary_list_rel decimal bl /\
    binary_list_to_string_rel bl bl_str /\
    output = "db" ++ bl_str ++ "db".
