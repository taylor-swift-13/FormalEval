
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (97 <=? n) (n <=? 122).

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (65 <=? n) (n <=? 90).

Definition is_alpha (c : ascii) : bool :=
  orb (is_lower c) (is_upper c).

Definition to_lower (c : ascii) : ascii :=
  if is_upper c then ascii_of_nat (nat_of_ascii c + 32) else c.

Definition to_upper (c : ascii) : ascii :=
  if is_lower c then ascii_of_nat (nat_of_ascii c - 32) else c.

Definition swapcase (c : ascii) : ascii :=
  if is_lower c then to_upper c
  else if is_upper c then to_lower c
  else c.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (list_to_string rest)
  end.

Definition has_letter (s : string) : bool :=
  existsb is_alpha (string_to_list s).

Definition swap_all_cases (s : string) : string :=
  list_to_string (map swapcase (string_to_list s)).

Definition reverse_string (s : string) : string :=
  list_to_string (rev (string_to_list s)).

Definition solve_spec (s : string) (result : string) : Prop :=
  (has_letter s = true -> result = swap_all_cases s) /\
  (has_letter s = false -> result = reverse_string s).
