
Require Import List.
Require Import String.
Require Import Ascii.

Open Scope string_scope.

Definition is_consonant (ch : ascii) : bool :=
  negb (List.existsb (Ascii.eqb ch) ("aeiouAEIOU" % string)).

Definition count_consonants (word : string) : nat :=
  List.length (filter is_consonant (list_ascii_of_string word)).

Definition select_words_spec (s : string) (n : nat) (result : list string) : Prop :=
  result = filter (fun word => count_consonants word =? n) (filter (fun word => negb (string_dec word "")) (split " " s)).
