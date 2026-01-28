Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义单个字符的解密操作 *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  (* Adjusted logic to handle all byte values consistent with Python's (ord(c) - 97 - 5) % 26 *)
  ascii_of_nat (a + (n + 2) mod 26).

(* Pre: no special constraints for `decode_shift` *)
Definition problem_50_pre (l' : string) : Prop := True.

(* decode_shift 程序的规约 *)
Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

(* Helper definition for the input string containing extended ASCII characters *)
Definition input_str : string :=
  String (ascii_of_nat 233) (
  String (ascii_of_nat 238) (
  "worhello worldld" ++ 
  String (ascii_of_nat 248) (
  String (ascii_of_nat 252) (
  String (ascii_of_nat 241) "")))).

Example test_problem_50 :
  problem_50_spec input_str "bgrjmczggjirjmgygyquj".
Proof.
  unfold problem_50_spec.
  unfold input_str.
  reflexivity.
Qed.