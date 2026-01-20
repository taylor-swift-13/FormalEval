
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Definition is_palindrome_spec (text : string) (res : bool) : Prop :=
  res = (text =? String.rev text).
