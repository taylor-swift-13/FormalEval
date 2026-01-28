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

Example test_sort_even_case : sort_even_spec 
  [4; -2; -12; -9; 23; 2; 3; 11; 12; -10; 4; -12; 4] 
  [-12; -2; 3; -9; 4; 2; 4; 11; 4; -10; 12; -12; 23].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        transitivity (-12 :: 4 :: 23 :: 3 :: 12 :: 4 :: 4 :: []).
        { apply perm_swap. }
        apply perm_skip.
        transitivity (3 :: 4 :: 23 :: 12 :: 4 :: 4 :: []).
        { transitivity (4 :: 3 :: 23 :: 12 :: 4 :: 4 :: []). apply perm_skip. apply perm_swap. apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        transitivity (4 :: 23 :: 12 :: 4 :: []).
        { transitivity (23 :: 4 :: 12 :: 4 :: []). apply perm_skip. apply perm_swap. apply perm_swap. }
        apply perm_skip.
        transitivity (4 :: 23 :: 12 :: []).
        { transitivity (23 :: 4 :: 12 :: []). apply perm_skip. apply perm_swap. apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.