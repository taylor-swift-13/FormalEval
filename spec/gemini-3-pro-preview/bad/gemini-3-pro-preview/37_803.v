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
  [5; -6; 2; -3; 3; -9; 0; 1; -9; -10; 2] 
  [-9; -6; 0; -3; 2; -9; 2; 1; 3; -10; 5].
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
        apply Permutation_trans with (-9 :: [5; 2; 3; 0] ++ [2]).
        { apply Permutation_sym.
          change [5; 2; 3; 0; -9; 2] with ([5; 2; 3; 0] ++ -9 :: [2]).
          apply Permutation_middle. }
        apply Permutation_skip.
        
        apply Permutation_trans with (0 :: [5; 2; 3] ++ [2]).
        { apply Permutation_sym.
          change [5; 2; 3; 0; 2] with ([5; 2; 3] ++ 0 :: [2]).
          apply Permutation_middle. }
        apply Permutation_skip.
        
        apply Permutation_trans with (2 :: [5] ++ [3; 2]).
        { apply Permutation_sym.
          change [5; 2; 3; 2] with ([5] ++ 2 :: [3; 2]).
          apply Permutation_middle. }
        apply Permutation_skip.
        
        apply Permutation_trans with (2 :: [5; 3] ++ []).
        { apply Permutation_sym.
          change [5; 3; 2] with ([5; 3] ++ 2 :: []).
          apply Permutation_middle. }
        apply Permutation_skip.
        
        apply Permutation_swap.
      * simpl.
        repeat constructor; try lia.
Qed.