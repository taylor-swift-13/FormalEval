(* """ Return length of given string
>>> strlen('')
0
>>> strlen('abc')
3
""" *)

(* ​	Spec(input : string, output : int) :=

​		output = length(input) *)
Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.