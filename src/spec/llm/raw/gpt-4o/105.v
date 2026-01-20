
Require Import List.
Require Import Nat.
Require Import String.

Definition to_word_spec (x : nat) (word : string) : Prop :=
  (x = 1 -> word = "One") /\
  (x = 2 -> word = "Two") /\
  (x = 3 -> word = "Three") /\
  (x = 4 -> word = "Four") /\
  (x = 5 -> word = "Five") /\
  (x = 6 -> word = "Six") /\
  (x = 7 -> word = "Seven") /\
  (x = 8 -> word = "Eight") /\
  (x = 9 -> word = "Nine").

Definition by_length_spec (arr : list nat) (result : list string) : Prop :=
  let filtered := filter (fun x => (1 <=? x) && (x <=? 9)) arr in
  let sorted := rev (sort Nat.leb filtered) in
  Forall2 to_word_spec sorted result.
