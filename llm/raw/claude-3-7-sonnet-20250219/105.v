
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Bool.
Require Import String.
Open Scope string_scope.

Definition is_between_1_and_9 (x : nat) : bool :=
  (1 <=? x) && (x <=? 9).

Definition to_word (x : nat) : string :=
  if x =? 1 then "One"
  else if x =? 2 then "Two"
  else if x =? 3 then "Three"
  else if x =? 4 then "Four"
  else if x =? 5 then "Five"
  else if x =? 6 then "Six"
  else if x =? 7 then "Seven"
  else if x =? 8 then "Eight"
  else "Nine".

Fixpoint filter_between_1_9 (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if is_between_1_and_9 x then x :: filter_between_1_9 xs
               else filter_between_1_9 xs
  end.

Definition sorted_rev (l : list nat) (l_sorted : list nat) : Prop :=
  NoDup l_sorted /\
  (forall x, In x l_sorted -> In x l) /\
  (forall x, In x l -> 1 <= x <= 9 -> In x l_sorted) /\
  Sorted Nat.lt l_sorted /\
  l_sorted = rev l_sorted.

Definition sorted_rev_filtered (l : list nat) (l_out : list nat) : Prop :=
  let filtered := filter_between_1_9 (sort Nat.lt l) in
  l_out = map to_word (rev filtered).

Definition by_length_spec (arr : list nat) (result : list string) : Prop :=
  result = map to_word
             (rev
               (filter (fun x => (1 <=? x) && (x <=? 9)) (sort Nat.lt arr))).
