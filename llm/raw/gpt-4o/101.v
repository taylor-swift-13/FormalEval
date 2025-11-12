
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition words_string_spec (s : string) (words : list string) : Prop :=
  let replaced := String.replace "," " " s in
  let split := String.split " " replaced in
  words = filter (fun word => negb (String.eqb word "")) split.
