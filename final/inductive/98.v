(* def count_upper(s):
"""
Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper('aBCdEf') returns 1
count_upper('abcdefg') returns 0
count_upper('dBBE') returns 0
""" *)

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Inductive is_uppercase_vowel : ascii -> Prop :=
| iuv_A : is_uppercase_vowel "A"%char
| iuv_E : is_uppercase_vowel "E"%char
| iuv_I : is_uppercase_vowel "I"%char
| iuv_O : is_uppercase_vowel "O"%char
| iuv_U : is_uppercase_vowel "U"%char.

Inductive count_upper_vowels_at_even_pos_rel : string -> nat -> nat -> Prop :=
| cuve_empty : forall i, count_upper_vowels_at_even_pos_rel "" i 0%nat
| cuve_match : forall c s i n, Nat.even i = true -> is_uppercase_vowel c ->
    count_upper_vowels_at_even_pos_rel s (S i) n ->
    count_upper_vowels_at_even_pos_rel (String c s) i (S n)
| cuve_skip : forall c s i n, (Nat.even i = false \/ ~ is_uppercase_vowel c) ->
    count_upper_vowels_at_even_pos_rel s (S i) n ->
    count_upper_vowels_at_even_pos_rel (String c s) i n.

Definition count_upper_spec (s : string) (output : nat) : Prop :=
  count_upper_vowels_at_even_pos_rel s 0%nat output.

