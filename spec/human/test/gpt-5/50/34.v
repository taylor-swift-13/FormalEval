Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

(* 定义单个字符的解密操作 *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

(* Pre: no special constraints for `decode_shift` *)
Definition problem_50_pre (l' : string) : Prop := True.

(* decode_shift 程序的规约 *)
Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

Example problem_50_test_case :
  problem_50_pre "uenrgscamkc" ->
  problem_50_spec "uenrgscamkc" "pzimbnxvhfx".
Proof.
  intros _. unfold problem_50_spec.
  vm_compute.
  reflexivity.
Qed.