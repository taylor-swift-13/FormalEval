
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.

Definition sort_array_spec (array sorted_array : list nat) : Prop :=
  (array = [] -> sorted_array = []) /\
  (array <> [] ->
    let sum := hd 0 array + last array 0 in
    Permutation array sorted_array /\
    ((sum mod 2 = 1 -> sorted_array = List.sort Nat.leb array) /\
     (sum mod 2 = 0 -> sorted_array = rev (List.sort Nat.leb array)))).
