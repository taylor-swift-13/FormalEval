Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义单个字符的解密操作 *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  ascii_of_nat ((97 + (n + 2) mod 26)%nat).

(* Pre: no special constraints for `decode_shift` *)
Definition problem_50_pre (l' : string) : Prop := True.

(* decode_shift 程序的规约 *)
Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

Definition input_str : string :=
  "abcworhdldddefthe quick brpown fox jumps orlazy dogghijklmnopqrsttuv" ++
  String (ascii_of_nat 238) (String (ascii_of_nat 248) (String (ascii_of_nat 252)
  ("hello world" ++ String (ascii_of_nat 241) "rldyz"))).

Definition output_str : string :=
  "vwxrjmcygyyyzaoczilpdxfiwmkjriiajsiephknijmgvutiyjbbcdefghijklmnoopqgquczggjirjmgyjmgytu".

Example test_problem_50 :
  problem_50_spec input_str output_str.
Proof.
  unfold problem_50_spec, input_str, output_str.
  reflexivity.
Qed.