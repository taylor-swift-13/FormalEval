
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Inductive key_type : Type :=
  | StringKey : string -> key_type
  | OtherKey : key_type.

Definition is_lower_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (Nat.leb 65 n) (Nat.leb n 90).

Fixpoint string_is_lower (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => andb (is_lower_char c) (string_is_lower rest)
  end.

Fixpoint string_is_upper (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => andb (is_upper_char c) (string_is_upper rest)
  end.

Definition is_string_key (k : key_type) : bool :=
  match k with
  | StringKey _ => true
  | OtherKey => false
  end.

Definition key_is_lower (k : key_type) : bool :=
  match k with
  | StringKey s => string_is_lower s
  | OtherKey => false
  end.

Definition key_is_upper (k : key_type) : bool :=
  match k with
  | StringKey s => string_is_upper s
  | OtherKey => false
  end.

Definition all_keys_lower (keys : list key_type) : bool :=
  forallb key_is_lower keys.

Definition all_keys_upper (keys : list key_type) : bool :=
  forallb key_is_upper keys.

Definition all_keys_strings (keys : list key_type) : bool :=
  forallb is_string_key keys.

Definition check_dict_case_spec (keys : list key_type) (result : bool) : Prop :=
  match keys with
  | [] => result = false
  | _ => result = (andb (all_keys_strings keys) (orb (all_keys_lower keys) (all_keys_upper keys)))
  end.
