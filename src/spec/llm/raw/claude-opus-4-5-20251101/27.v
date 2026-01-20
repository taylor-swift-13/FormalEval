
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_lowercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (97 <=? n) (n <=? 122).

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (65 <=? n) (n <=? 90).

Definition to_lowercase (c : ascii) : ascii :=
  if is_uppercase c then
    ascii_of_nat (nat_of_ascii c + 32)
  else
    c.

Definition to_uppercase (c : ascii) : ascii :=
  if is_lowercase c then
    ascii_of_nat (nat_of_ascii c - 32)
  else
    c.

Definition swap_case (c : ascii) : ascii :=
  if is_lowercase c then to_uppercase c
  else if is_uppercase c then to_lowercase c
  else c.

Fixpoint flip_case_list (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | c :: rest => swap_case c :: flip_case_list rest
  end.

Definition flip_case_spec (input : string) (output : string) : Prop :=
  let input_list := list_ascii_of_string input in
  let output_list := list_ascii_of_string output in
  output_list = flip_case_list input_list.
