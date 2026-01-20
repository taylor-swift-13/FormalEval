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
  [5; 3; -5; 2; -2; 4; 3; -9; 2; 0; 1; 9; -10; 12] 
  [-10; 3; -5; 2; -2; 4; 1; -9; 2; 0; 3; 9; 5; 12].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (-10 :: [5; -5; -2; 3; 2; 1]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_cons.
        transitivity (1 :: [5; 3; 2]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (2 :: [5; 3]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; try lia ]).
        apply Sorted_nil.
Qed.