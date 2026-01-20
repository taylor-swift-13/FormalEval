
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition is_palindrome_spec (string : string) (result : bool) : Prop :=
  result = (string =? (String.rev string))%string.

Definition make_palindrome_spec (string : string) (result : string) : Prop :=
  (is_palindrome_spec string true -> result = string) /\
  (forall i : nat,
      i < String.length string ->
      is_palindrome_spec (String.substring i (String.length string - i) string) true ->
      result = string ++ String.rev (String.substring 0 i string)).
