
Require Import List.
Require Import Arith.
Require Import Lia.

Definition strange_sort_list_spec (lst : list nat) (sorted_lst : list nat) (ans : list nat) : Prop :=
  sorted_lst = sort Nat.leb lst /\
  exists i j,
    i = 0 /\ j = length sorted_lst - 1 /\
    (forall k,
      k < length sorted_lst ->
      (k mod 2 = 0 -> nth k ans 0 = nth (i + k / 2) sorted_lst 0) /\
      (k mod 2 = 1 -> nth k ans 0 = nth (j - k / 2) sorted_lst 0)) /\
    length ans = length sorted_lst.
