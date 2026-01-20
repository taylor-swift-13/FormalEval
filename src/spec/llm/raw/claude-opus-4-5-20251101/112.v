
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition char := Ascii.ascii.

Definition char_in_string (ch : char) (c : list char) : bool :=
  existsb (Ascii.eqb ch) c.

Fixpoint filter_chars (s : list char) (c : list char) : list char :=
  match s with
  | [] => []
  | h :: t => if char_in_string h c then filter_chars t c
              else h :: filter_chars t c
  end.

Definition is_palindrome (s : list char) : bool :=
  list_eq_dec Ascii.ascii_dec s (rev s).

Definition is_palindrome_prop (s : list char) : Prop :=
  s = rev s.

Definition reverse_delete_spec (s : list char) (c : list char) 
                               (result : list char) (is_palin : bool) : Prop :=
  result = filter_chars s c /\
  is_palin = true <-> is_palindrome_prop result.
