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

Example test_sort_even_case : 
  sort_even_spec 
    [6; 1; 2; 4; 3; 4; 5; 6; 7; 10; 4; 4] 
    [2; 1; 3; 4; 4; 4; 5; 6; 6; 10; 7; 4].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (2 :: 6 :: 3 :: 5 :: 7 :: 4 :: []).
        { apply perm_swap. }
        apply perm_skip.
        transitivity (3 :: 6 :: 5 :: 7 :: 4 :: []).
        { apply perm_swap. }
        apply perm_skip.
        transitivity (4 :: 6 :: 5 :: 7 :: []).
        { 
          transitivity (6 :: 5 :: 4 :: 7 :: []).
          - repeat apply perm_skip. apply perm_swap.
          - transitivity (6 :: 4 :: 5 :: 7 :: []).
            + apply perm_skip. apply perm_swap.
            + apply perm_swap.
        }
        apply perm_skip.
        transitivity (5 :: 6 :: 7 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.