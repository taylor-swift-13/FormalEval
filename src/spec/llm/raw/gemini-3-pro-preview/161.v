
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (97 <=? n) && (n <=? 122).

Definition is_alpha (c : ascii) : bool :=
  is_upper c || is_lower c.

Definition swap_case_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else c.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (list_to_string l')
  end.

Definition solve_spec (s : string) (result : string) : Prop :=
  let chars := string_to_list s in
  let has_letter := existsb is_alpha chars in
  if has_letter then
    result = list_to_string (map swap_case_char chars)
  else
    result = list_to_string (rev chars).
