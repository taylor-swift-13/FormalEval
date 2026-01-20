
Require Import String.
Require Import Ascii.

Definition is_upper (c : ascii) : bool :=
  (c >= "A")%char && (c <= "Z")%char.

Definition is_lower (c : ascii) : bool :=
  (c >= "a")%char && (c <= "z")%char.

Definition to_lower (c : ascii) : ascii :=
  if is_upper c then ascii_of_nat (nat_of_ascii c + 32) else c.

Definition to_upper (c : ascii) : ascii :=
  if is_lower c then ascii_of_nat (nat_of_ascii c - 32) else c.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a" | "e" | "i" | "o" | "u" | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Definition shift_vowel (c : ascii) : ascii :=
  if is_vowel c then ascii_of_nat (nat_of_ascii c + 2) else c.

Definition switch_case (c : ascii) : ascii :=
  if is_upper c then to_lower c else to_upper c.

Fixpoint encode_spec (message : string) (result : string) : Prop :=
  match message, result with
  | EmptyString, EmptyString => True
  | String c1 s1, String c2 s2 => 
      switch_case c1 = shift_vowel c2 /\ encode_spec s1 s2
  | _, _ => False
  end.
