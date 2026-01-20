
Require Import List String Ascii.
Import ListNotations.

Definition odd_count_spec (lst : list string) (output : list string) : Prop :=
  let template := "the number of odd elements in the string i of the input." in
  output = map (fun s => 
    let odd_cnt := length (filter (fun ch => Nat.odd (ascii_to_nat ch)) (list_ascii_of_string s)) in
    string_replace "i" (string_of_nat odd_cnt) template
  ) lst.
