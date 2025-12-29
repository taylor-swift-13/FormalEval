(* def same_chars(s0: str, s1: str):
"""
Check if two words have the same characters.
>>> same_chars('eabcdzzzz', 'dddzzzzzzzddeddabc')
True
>>> same_chars('abcd', 'dddddddabc')
True
>>> same_chars('dddddddabc', 'abcd')
True
>>> same_chars('eabcd', 'dddddddabc')
False
>>> same_chars('abcd', 'dddddddabce')
False
>>> same_chars('eabcdzzzz', 'dddzzzzzzzddddabc')
False
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.


(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : list ascii) : Prop := True.

Definition problem_54_spec (s0 s1 : list ascii) (b : bool) : Prop :=
  b = true <-> (forall (c : ascii), In c s0 <-> In c s1).