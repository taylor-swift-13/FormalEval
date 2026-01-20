
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

Import ListNotations.

Open Scope Z_scope.

Definition is_sorted (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    nth i l 0 <= nth j l 0.

Definition is_permutation (l1 l2 : list Z) : Prop :=
  Permutation l1 l2.

Definition has_second_smallest (lst : list Z) (result : Z) : Prop :=
  exists sorted_lst : list Z,
    is_permutation lst sorted_lst /\
    is_sorted sorted_lst /\
    exists i : nat,
      (i < length sorted_lst)%nat /\
      nth i sorted_lst 0 <> nth 0 sorted_lst 0 /\
      result = nth i sorted_lst 0 /\
      (forall j : nat, (0 < j < i)%nat -> nth j sorted_lst 0 = nth 0 sorted_lst 0).

Definition no_second_smallest (lst : list Z) : Prop :=
  length lst <= 1 \/
  (forall x : Z, In x lst -> x = nth 0 (sort lst) 0).

Definition next_smallest_spec (lst : list Z) (result : option Z) : Prop :=
  match result with
  | None => length lst <= 1 \/ 
            (exists sorted_lst : list Z,
              is_permutation lst sorted_lst /\
              is_sorted sorted_lst /\
              forall i : nat, (i < length sorted_lst)%nat -> 
                nth i sorted_lst 0 = nth 0 sorted_lst 0)
  | Some r => length lst > 1 /\
              has_second_smallest lst r
  end.
