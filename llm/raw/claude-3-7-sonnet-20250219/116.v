
Require Import List.
Require Import Nat.
Import ListNotations.

Fixpoint count_ones (n : nat) : nat :=
  match n with
  | 0 => 0
  | _ => (n mod 2) + count_ones (n / 2)
  end.

Fixpoint sorted_by_ones_and_value (l : list nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: y :: t =>
    (count_ones x < count_ones y \/
     (count_ones x = count_ones y /\ x <= y)) /\
    sorted_by_ones_and_value (y :: t)
  end.

Definition sort_array_spec (arr sorted_arr : list nat) : Prop :=
  Permutation.arr_perm arr sorted_arr /\
  sorted_by_ones_and_value sorted_arr.
