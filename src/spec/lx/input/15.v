(* """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
'0'
>>> string_sequence(5)
'0 1 2 3 4 5'
""" *)

(*  *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* 假设有一个函数把自然数转成字符串 *)
Parameter string_of_nat : nat -> string.

(* 用来连接数字字符串，中间用空格隔开 *)
Fixpoint seq_string (start limit : nat) : string :=
  match limit with
  | 0 => string_of_nat start
  | S n' => string_of_nat start ++ " " ++ seq_string (S start) n'
  end.

(* 规约 Spec *)
Definition Spec (n : nat) (output : string) : Prop :=
  output = seq_string 0 n.
