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
  [5; 3; -5; 11; -3; 2; 3; -9; 0; 123; 1; -10; 3; 3; 123] 
  [-5; 3; -3; 11; 0; 2; 1; -9; 3; 123; 3; -10; 5; 3; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (-5 :: [5; -3; 3; 0; 1; 3; 123]).
        { apply Permutation_swap. }
        apply Permutation_skip.
        transitivity (-3 :: [5; 3; 0; 1; 3; 123]).
        { apply Permutation_swap. }
        apply Permutation_skip.
        transitivity (3 :: 5 :: 0 :: [1; 3; 123]).
        { apply Permutation_swap. }
        transitivity (3 :: 0 :: 5 :: [1; 3; 123]).
        { apply Permutation_skip. apply Permutation_swap. }
        transitivity (0 :: 3 :: 5 :: [1; 3; 123]).
        { apply Permutation_swap. }
        apply Permutation_skip.
        transitivity (5 :: 3 :: 1 :: [3; 123]).
        { apply Permutation_swap. }
        transitivity (5 :: 1 :: 3 :: [3; 123]).
        { apply Permutation_skip. apply Permutation_swap. }
        transitivity (1 :: 5 :: 3 :: [3; 123]).
        { apply Permutation_swap. }
        apply Permutation_skip.
        transitivity (3 :: 5 :: 3 :: [123]).
        { apply Permutation_swap. }
        apply Permutation_skip.
        transitivity (3 :: 5 :: [123]).
        { apply Permutation_swap. }
        apply Permutation_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || (apply HdRel_cons; lia)).
Qed.