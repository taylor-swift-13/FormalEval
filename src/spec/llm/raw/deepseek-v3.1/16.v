
Require Import String List Ascii.
Require Import ZArith.

Definition to_lower (s : string) : string :=
  map (fun c => if ascii_dec c "A" then "a" else
               if ascii_dec c "B" then "b" else
               if ascii_dec c "C" then "c" else
               if ascii_dec c "D" then "d" else
               if ascii_dec c "E" then "e" else
               if ascii_dec c "F" then "f" else
               if ascii_dec c "G" then "g" else
               if ascii_dec c "H" then "h" else
               if ascii_dec c "I" then "i" else
               if ascii_dec c "J" then "j" else
               if ascii_dec c "K" then "k" else
               if ascii_dec c "L" then "l" else
               if ascii_dec c "M" then "m" else
               if ascii_dec c "N" then "n" else
               if ascii_dec c "O" then "o" else
               if ascii_dec c "P" then "p" else
               if ascii_dec c "Q" then "q" else
               if ascii_dec c "R" then "r" else
               if ascii_dec c "S" then "s" else
               if ascii_dec c "T" then "t" else
               if ascii_dec c "U" then "u" else
               if ascii_dec c "V" then "v" else
               if ascii_dec c "W" then "w" else
               if ascii_dec c "X" then "x" else
               if ascii_dec c "Y" then "y" else
               if ascii_dec c "Z" then "z" else c) s.

Fixpoint remove_duplicates (l : list ascii) : list ascii :=
  match l with
  | nil => nil
  | h :: t => h :: remove_duplicates (filter (fun x => negb (eqb x h)) t)
  end.

Definition count_distinct_characters_spec (s : string) (result : nat) : Prop :=
  result = length (remove_duplicates (list_ascii_of_string (to_lower s))).
