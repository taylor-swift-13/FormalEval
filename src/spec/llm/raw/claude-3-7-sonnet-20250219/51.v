
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition remove_vowels_spec (text result : string) : Prop :=
  let vowels := "aeiouAEIOU" in
  let is_vowel (ch : ascii) := existsb (fun v => if ascii_dec ch v then true else false) (list_ascii_of_string vowels) in
  result = String.concat "" (filter (fun ch => negb (is_vowel ch)) (list_ascii_of_string text)).

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.
