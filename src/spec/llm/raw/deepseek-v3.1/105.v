
Require Import List ZArith.
Import ListNotations.

Definition to_word (x : Z) : string :=
  if x =? 1 then "One"
  else if x =? 2 then "Two"
  else if x =? 3 then "Three"
  else if x =? 4 then "Four"
  else if x =? 5 then "Five"
  else if x =? 6 then "Six"
  else if x =? 7 then "Seven"
  else if x =? 8 then "Eight"
  else "Nine".

Definition by_length_spec (arr : list Z) (result : list string) : Prop :=
  let filtered := filter (fun x => 1 <=? x <=? 9) arr in
  let sorted := rev (sort Z.leb filtered) in
  result = map to_word sorted.
