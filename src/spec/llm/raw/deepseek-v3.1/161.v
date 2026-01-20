
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Definition solve_spec (s : string) (result : string) : Prop :=
  (exists has_letter : bool,
    (fix process (chars : list ascii) (acc : string) (has_letter : bool) : (string * bool) :=
      match chars with
      | nil => (acc, has_letter)
      | ch :: rest =>
          if is_alpha ch then
            process rest (acc ++ String (swapcase ch)) true
          else
            process rest (acc ++ String ch) has_letter
      end) (list_ascii_of_string s) "" has_letter = (result, true)) \/
  (~exists ch : ascii, In ch (list_ascii_of_string s) /\ is_alpha ch) /\
  result = rev s.
