Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith. (* For nat arithmetic like mod *)
Import ListNotations.

(* 定义单个字符的解密操作 (最终正确版) *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a" in
  ascii_of_nat (a + (n - a + 21) mod 26).

(* decode_shift 程序的规约 (版本: list ascii) *)
Definition decode_shift_spec (l' l : list ascii) : Prop :=
  l = map decode_char l'.