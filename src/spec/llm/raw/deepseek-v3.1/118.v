
Require Import String.
Require Import List.
Require Import Bool.

Definition is_vowel (ch : ascii) : bool :=
  match ch with
  | "a" | "e" | "i" | "o" | "u" | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Definition get_closest_vowel_spec (word : list ascii) (result : list ascii) : Prop :=
  (exists i, 
    (i < length word - 2) /\
    (i > 0) /\
    is_vowel (nth i word " ") = true /\
    is_vowel (nth (i-1) word " ") = false /\
    is_vowel (nth (i+1) word " ") = false /\
    (forall j, j > i -> j < length word - 1 -> 
      ~(is_vowel (nth j word " ") = true /\
        is_vowel (nth (j-1) word " ") = false /\
        is_vowel (nth (j+1) word " ") = false)) /\
    result = [nth i word " "]) \/
  (~(exists i, 
      (i < length word - 2) /\
      (i > 0) /\
      is_vowel (nth i word " ") = true /\
      is_vowel (nth (i-1) word " ") = false /\
      is_vowel (nth (i+1) word " ") = false) /\
    result = []).
