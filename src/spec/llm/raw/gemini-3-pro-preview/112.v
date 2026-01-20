
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition reverse_delete_spec (s : string) (c : string) (result : string * bool) : Prop :=
  let (ss, is_pal) := result in
  let s_chars := list_ascii_of_string s in
  let c_chars := list_ascii_of_string c in
  let keep_char (ch : ascii) : bool := negb (existsb (Ascii.eqb ch) c_chars) in
  let filtered_s := string_of_list_ascii (filter keep_char s_chars) in
  ss = filtered_s /\ is_pal = (ss =? string_rev ss).
