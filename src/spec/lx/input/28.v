(*  Concatenate list of strings into a single string
>>> concatenate([])
''
>>> concatenate(['a', 'b', 'c'])
'abc' *)

(* Spec(input : list string, output : string) :=

​	Concat(input, output) *)

Require Import List String.
Import ListNotations.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.