
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_palindrome (s : string) : bool :=
  s =? string_rev s.

Definition reverse_delete_spec (s c : string) (result : string) (is_palindrome_check : bool) : Prop :=
  let filtered := filter (fun ch => negb (existsb (fun ch_c => ch =? ch_c) (list_of_string c))) (list_of_string s) in
  result = string_of_list filtered /\
  is_palindrome_check = is_palindrome result.
