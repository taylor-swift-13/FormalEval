
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition remove_vowels_spec (text : string) (result : string) : Prop :=
  result = String.concat "" (filter (fun ch => negb (String.contains "aeiouAEIOU" ch)) (list_of_string text)).
