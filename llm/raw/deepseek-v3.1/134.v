
Require Import String.
Require Import Ascii.

Definition check_if_last_char_is_a_letter_spec (txt : string) (result : bool) : Prop :=
  result = match txt with
  | "" => false
  | String ch "" => is_alpha ch
  | String _ (String ch_last "" as rest) =>
      is_alpha ch_last && (String.get (substring 0 (length rest - 1) rest) (length rest - 2) = Some " ")%char
  | _ => false
  end.
