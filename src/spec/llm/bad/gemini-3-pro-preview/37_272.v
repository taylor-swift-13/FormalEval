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
  [4; 2; 2; 0; 9; 5; -3; 2; 8; 3; 7; 2; 2; 8; 2; 2] 
  [-3; 2; 2; 0; 2; 5; 2; 2; 4; 3; 7; 2; 8; 8; 9; 2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -3 :: [4; 2; 9; 8; 7; 2; 2]).
        2: apply perm_skip.
        1: {
           change [4; 2; 9; -3; 8; 7; 2; 2] with ([4; 2; 9] ++ -3 :: [8; 7; 2; 2]).
           apply Permutation_sym. apply Permutation_middle.
        }
        apply Permutation_trans with (l' := 2 :: [4; 9; 8; 7; 2; 2]).
        2: apply perm_skip.
        1: {
           change [4; 2; 9; 8; 7; 2; 2] with ([4] ++ 2 :: [9; 8; 7; 2; 2]).
           apply Permutation_sym. apply Permutation_middle.
        }
        apply Permutation_trans with (l' := 2 :: [4; 9; 8; 7; 2]).
        2: apply perm_skip.
        1: {
           change [4; 9; 8; 7; 2; 2] with ([4; 9; 8; 7] ++ 2 :: [2]).
           apply Permutation_sym. apply Permutation_middle.
        }
        apply Permutation_trans with (l' := 2 :: [4; 9; 8; 7]).
        2: apply perm_skip.
        1: {
           change [4; 9; 8; 7; 2] with ([4; 9; 8; 7] ++ 2 :: []).
           apply Permutation_sym. apply Permutation_middle.
        }
        apply perm_skip.
        apply Permutation_trans with (l' := 7 :: [9; 8]).
        2: apply perm_skip.
        1: {
           change [9; 8; 7] with ([9; 8] ++ 7 :: []).
           apply Permutation_sym. apply Permutation_middle.
        }
        apply perm_swap.
      * simpl.
        repeat (constructor; try lia).
Qed.