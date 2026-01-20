
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Fixpoint get_even_indices {A : Type} (l : list A) (idx : nat) : list A :=
  match l with
  | [] => []
  | x :: xs => if Nat.even idx then x :: get_even_indices xs (S idx)
               else get_even_indices xs (S idx)
  end.

Fixpoint get_odd_indices {A : Type} (l : list A) (idx : nat) : list A :=
  match l with
  | [] => []
  | x :: xs => if Nat.odd idx then x :: get_odd_indices xs (S idx)
               else get_odd_indices xs (S idx)
  end.

Fixpoint nth_error_default {A : Type} (l : list A) (n : nat) (default : A) : A :=
  match l, n with
  | [], _ => default
  | x :: _, 0 => x
  | _ :: xs, S n' => nth_error_default xs n' default
  end.

Definition sort_even_spec (l : list nat) (l' : list nat) : Prop :=
  let evens := get_even_indices l 0 in
  let sorted_evens := sort Nat.leb evens in
  length l' = length l /\
  (forall i, i < length l -> 
    Nat.odd i = true -> 
    nth_error l' i = nth_error l i) /\
  (forall i, i < length l -> 
    Nat.even i = true -> 
    nth_error l' i = nth_error sorted_evens (i / 2)) /\
  Permutation (get_even_indices l' 0) (get_even_indices l 0) /\
  LocallySorted Nat.le (get_even_indices l' 0).
