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
  [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 2] 
  [2; 1; 2; 1; 3; 9; 4; 6; 5; 3; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate Hodd; reflexivity | simpl in Hlen ]).
      lia.
    + split.
      * simpl.
        transitivity (3 :: [2; 2] ++ [4; 5; 5]).
        2: apply Permutation_middle.
        apply perm_skip.
        
        transitivity (4 :: [2; 2] ++ [5; 5]).
        2: apply Permutation_middle.
        apply perm_skip.
        
        transitivity (5 :: [2; 2] ++ [5]).
        2: apply Permutation_middle.
        apply perm_skip.
        
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; simpl; lia ]).
        apply Sorted_nil.
Qed.