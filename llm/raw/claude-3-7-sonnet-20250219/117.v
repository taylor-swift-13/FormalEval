
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_consonant (ch : ascii) : bool :=
  let vowels := "aeiouAEIOU"%string in
  negb (existsb (Ascii.eqb ch) (list_ascii_of_string vowels)).

Fixpoint count_consonants (w : string) : nat :=
  match w with
  | EmptyString => 0
  | String ch rest =>
    (if is_consonant ch then 1 else 0) + count_consonants rest
  end.

Definition select_words_spec (s : string) (n : nat) (res : list string) : Prop :=
  (* Splitting s by spaces into words, ignoring empty words *)
  let words := filter (fun w => negb (String.eqb w "")) (split String.string_dec " " s) in
  res = filter (fun w => Nat.eqb (count_consonants w) n) words.
