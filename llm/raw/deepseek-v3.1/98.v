
Require Import String.
Require Import List.
Require Import Ascii.
Require Import Bool.

Definition is_uppercase_vowel (c : ascii) : bool :=
  match c with
  | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Fixpoint count_upper_spec (s : string) (cnt : nat) : Prop :=
  match s with
  | EmptyString => cnt = 0
  | String c1 EmptyString => 
      if is_uppercase_vowel c1 then cnt = 1 else cnt = 0
  | String c1 (String c2 rest) =>
      let rest_count := count_upper_spec rest 0 in
      if is_uppercase_vowel c1 
      then cnt = S (proj1_sig (exist _ _ rest_count))
      else cnt = proj1_sig (exist _ _ rest_count)
  end.
