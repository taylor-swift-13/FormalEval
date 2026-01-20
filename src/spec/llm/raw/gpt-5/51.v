
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.

Definition ascii_eq (a b : ascii) : bool :=
  if Ascii.ascii_dec a b then true else false.

Definition is_vowel (ch : ascii) : bool :=
  orb (ascii_eq ch "a"%char)
    (orb (ascii_eq ch "e"%char)
    (orb (ascii_eq ch "i"%char)
    (orb (ascii_eq ch "o"%char)
    (orb (ascii_eq ch "u"%char)
    (orb (ascii_eq ch "A"%char)
    (orb (ascii_eq ch "E"%char)
    (orb (ascii_eq ch "I"%char)
    (orb (ascii_eq ch "O"%char)
         (ascii_eq ch "U"%char)))))))).

Fixpoint filter_string (p : ascii -> bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String ch rest =>
      if p ch then filter_string p rest else String ch (filter_string p rest)
  end.

Definition remove_vowels_spec (text : string) (res : string) : Prop :=
  res = filter_string is_vowel text.
