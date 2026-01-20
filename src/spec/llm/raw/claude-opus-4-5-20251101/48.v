
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint reverse_list {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => reverse_list xs ++ [x]
  end.

Definition string_to_list (s : string) : list ascii :=
  list_ascii_of_string s.

Definition list_to_string (l : list ascii) : string :=
  string_of_list_ascii l.

Definition reverse_string (s : string) : string :=
  list_to_string (reverse_list (string_to_list s)).

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  result = true <-> text = reverse_string text.
