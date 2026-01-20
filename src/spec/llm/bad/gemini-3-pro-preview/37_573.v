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
  [-5; -7; 2; 10; 0; 5; 123; -3; 2; 8; 3; 7; 0] 
  [-5; -7; 0; 10; 0; 5; 2; -3; 2; 8; 3; 7; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in *; try discriminate; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (0 :: 2 :: 123 :: 2 :: 3 :: 0 :: []).
        { apply Permutation_swap. }
        apply Permutation_cons.
        change (2 :: 123 :: 2 :: 3 :: 0 :: []) with ((2 :: 123 :: 2 :: 3 :: []) ++ 0 :: []).
        transitivity (0 :: (2 :: 123 :: 2 :: 3 :: []) ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl.
        apply Permutation_cons.
        apply Permutation_cons.
        transitivity (2 :: 123 :: 3 :: []).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.