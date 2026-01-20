
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition digit_to_word (x : Z) : string :=
  match x with
  | 1 => "One"
  | 2 => "Two"
  | 3 => "Three"
  | 4 => "Four"
  | 5 => "Five"
  | 6 => "Six"
  | 7 => "Seven"
  | 8 => "Eight"
  | 9 => "Nine"
  | _ => ""
  end.

Definition is_valid_digit (x : Z) : bool :=
  (1 <=? x) && (x <=? 9).

Definition by_length_spec (arr : list Z) (ans : list string) : Prop :=
  exists (l : list Z),
    Permutation l (filter is_valid_digit arr) /\
    Sorted Z.ge l /\
    ans = map digit_to_word l.
