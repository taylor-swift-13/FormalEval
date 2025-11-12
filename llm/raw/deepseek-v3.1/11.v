
Require Import List String Ascii.
Import ListNotations.

Definition string_xor_spec (a : list ascii) (b : list ascii) (result : list ascii) : Prop :=
  length a = length b /\
  result = map (fun p => if ascii_dec (fst p) (snd p) then "0"%char else "1"%char) (combine a b).
