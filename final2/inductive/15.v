(* """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
'0'
>>> string_sequence(5)
'0 1 2 3 4 5'
""" *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(* 假设有一个函数把自然数转成字符串 *)
Parameter string_of_nat : nat -> string.

Inductive seq_string_rel : nat -> nat -> string -> Prop :=
  | ssr_zero : forall start, seq_string_rel start 0 (string_of_nat start)
  | ssr_succ : forall start limit n' result,
      limit = S n' ->
      seq_string_rel (S start) n' result ->
      seq_string_rel start limit (string_of_nat start ++ " " ++ result).


Definition Spec (n : nat) (output : string) : Prop :=
  seq_string_rel 0 n output.
