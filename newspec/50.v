（* def encode_shift(s: str):
"""
returns encoded string by shifting every character by 5 in the alphabet.
"""
return "".join([chr(((ord(ch) + 5 - ord("a")) % 26) + ord("a")) for ch in s])


def decode_shift(s: str):
"""
takes as input string encoded with encode_shift function. Returns decoded string.
""" *）
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith. (* For nat arithmetic like mod *)
Import ListNotations.

(* 定义单个字符的解密操作 *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a" in
  ascii_of_nat (a + (n - a + 21) mod 26).

(* Pre: no special constraints for `decode_shift` *)
Definition problem_50_pre (l' : list ascii) : Prop := True.

(* decode_shift 程序的规约 *)
Definition problem_50_spec (l' l : list ascii) : Prop :=
  l = map decode_char l'.