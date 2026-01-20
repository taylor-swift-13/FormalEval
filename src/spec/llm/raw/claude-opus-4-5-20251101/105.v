
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

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

Definition in_range (x : Z) : bool :=
  (1 <=? x) && (x <=? 9).

Definition filter_in_range (l : list Z) : list Z :=
  filter (fun x => in_range x) l.

Definition by_length_spec (arr : list Z) (result : list string) : Prop :=
  let filtered := filter_in_range arr in
  let sorted := rev (List.sort Z.leb filtered) in
  result = map to_word sorted.
