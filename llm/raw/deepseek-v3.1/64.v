
Require Import String List Ascii.

Definition is_vowel (ch : ascii) : bool :=
  match ch with
  | "a" | "e" | "i" | "o" | "u" | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Definition is_y (ch : ascii) : bool :=
  match ch with
  | "y" | "Y" => true
  | _ => false
  end.

Fixpoint vowels_count_spec (s : string) (result : nat) : Prop :=
  let vowels := length (filter is_vowel (list_ascii_of_string s)) in
  let last_char := 
    match s with
    | "" => None
    | _ => Some (nth (length s - 1) (list_ascii_of_string s) " "%char)
    end in
  result = vowels + (if match last_char with Some ch => is_y ch | None => false end then 1 else 0).
