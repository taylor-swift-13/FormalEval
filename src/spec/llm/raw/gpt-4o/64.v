
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.Ascii.

Definition is_vowel (ch : ascii) : bool :=
  ch = "a"%char \/ ch = "e"%char \/ ch = "i"%char \/ ch = "o"%char \/ ch = "u"%char \/
  ch = "A"%char \/ ch = "E"%char \/ ch = "I"%char \/ ch = "O"%char \/ ch = "U"%char.

Definition is_y_at_end (s : string) : bool :=
  match s with
  | EmptyString => false
  | String ch EmptyString => ch = "y"%char \/ ch = "Y"%char
  | _ => false
  end.

Fixpoint count_vowels (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest => if is_vowel ch then 1 + count_vowels rest else count_vowels rest
  end.

Definition vowels_count_spec (s : string) (count : nat) : Prop :=
  count = count_vowels s + (if is_y_at_end s then 1 else 0).
