
Require Import String.
Require Import Ascii.
Open Scope string_scope.

Definition is_vowel (ch : ascii) : bool :=
  match ch with
  | "a" | "e" | "i" | "o" | "u" | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Definition get_closest_vowel_spec (word : string) (result : string) : Prop :=
  (forall i,
    1 <= i < String.length word - 1 ->
    is_vowel (String.get i word) = true ->
    is_vowel (String.get (i - 1) word) = false ->
    is_vowel (String.get (i + 1) word) = false ->
    result = String.make 1 (String.get i word)) \/
  (result = "" /\ (forall i, 1 <= i < String.length word - 1 ->
    ~(is_vowel (String.get i word) = true /\
      is_vowel (String.get (i - 1) word) = false /\
      is_vowel (String.get (i + 1) word) = false))).
