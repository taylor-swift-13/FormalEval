(* def count_upper(s):
"""
Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper('aBCdEf') returns 1
count_upper('abcdefg') returns 0
count_upper('dBBE') returns 0
""" *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.

(*
  Defines a boolean function that checks if a character is an uppercase vowel.
  This returns 'true' or 'false' and is directly usable in computations.
*)
Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(*
  The program specification for count_upper.
  It relates an input string 's' to an output natural number 'n'.
*)
Definition count_upper_spec (s : string) (n : nat) : Prop :=
  n = length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).