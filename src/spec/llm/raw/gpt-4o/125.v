
Require Import List.
Require Import Ascii.
Require Import String.
Open Scope string_scope.

Definition split_words_spec (txt : string) (result : list string + nat) : Prop :=
  let whitespace := [" "; "\n"; "\r"; "\t"] in
  if existsb (fun x => String.contains txt x) whitespace then
    result = inl (String.split (fun x => existsb (Ascii.eqb x) whitespace) txt)
  else if String.contains txt "," then
    result = inl (String.split (Ascii.eqb ",") txt)
  else
    let cnt := fold_left (fun acc ch =>
      if (Ascii.is_lower ch) && ((Ascii.nat_of_ascii ch - Ascii.nat_of_ascii "a") mod 2 =? 1) then
        acc + 1
      else
        acc) (list_ascii_of_string txt) 0 in
    result = inr cnt.
