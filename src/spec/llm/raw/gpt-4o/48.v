
Require Import String.
Require Import Bool.

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
result = (text =? String.rev text)%string.
