
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Nat.

Open Scope char_scope.
Open Scope string_scope.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (97 <=? n) && (n <=? 122).

Definition switch_case_char (c : ascii) : ascii :=
  if is_upper c then
    ascii_of_nat (nat_of_ascii c + 32)
  else if is_lower c then
    ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a" | "e" | "i" | "o" | "u"
  | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Definition vowel_change_char (c : ascii) : ascii :=
  if is_vowel c then ascii_of_nat (nat_of_ascii c + 2) else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String ch rest => String (f ch) (map_string f rest)
  end.

Definition encode_spec (message encoded : string) : Prop :=
  let switched := map_string switch_case_char message in
  encoded = map_string vowel_change_char switched.
