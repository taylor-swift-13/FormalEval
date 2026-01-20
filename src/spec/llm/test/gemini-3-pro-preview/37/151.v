Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec [3; -3; 1; 1; 1; 2; 2; 2; 2; 3; 1] [1; -3; 1; 1; 1; 2; 2; 2; 2; 3; 3].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [1; 1; 2; 2; 1] ++ [3]).
        { apply Permutation_cons_append. }
        simpl.
        apply perm_skip.
        apply perm_skip.
        apply Permutation_trans with (l' := 2 :: 1 :: 2 :: [3]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * simpl.
        repeat (constructor; try lia).
Qed.