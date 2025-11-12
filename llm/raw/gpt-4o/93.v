
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition is_uppercase (ch : ascii) : bool :=
  let n := nat_of_ascii ch in
  (65 <=? n) && (n <=? 90).

Definition is_lowercase (ch : ascii) : bool :=
  let n := nat_of_ascii ch in
  (97 <=? n) && (n <=? 122).

Definition switch_case_spec (ch : ascii) (result : ascii) : Prop :=
  (is_uppercase ch = true -> result = ascii_of_nat (nat_of_ascii ch + 32)) /\
  (is_lowercase ch = true -> result = ascii_of_nat (nat_of_ascii ch - 32)) /\
  (~is_uppercase ch && ~is_lowercase ch = true -> result = ch).

Definition is_vowel (ch : ascii) : bool :=
  let vowels := ["a"; "e"; "i"; "o"; "u"; "A"; "E"; "I"; "O"; "U"]%char in
  List.existsb (fun v => v =? ch) vowels.

Definition vowel_change_spec (ch : ascii) (result : ascii) : Prop :=
  (is_vowel ch = true -> result = ascii_of_nat (nat_of_ascii ch + 2)) /\
  (is_vowel ch = false -> result = ch).

Definition encode_spec (message : list ascii) (encoded_message : list ascii) : Prop :=
  exists intermediate_message,
    (forall ch result, In ch message -> In result intermediate_message -> switch_case_spec ch result) /\
    (forall ch result, In ch intermediate_message -> In result encoded_message -> vowel_change_spec ch result).
