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
  [-5; -7; 11; -5; 2; 9; 5; -3; 2; 8; 7; 3; 7; 3; 3; 2] 
  [-5; -7; 2; -5; 2; 9; 3; -3; 5; 8; 7; 3; 7; 3; 11; 2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (11 :: [2; 2; 3; 5; 7; 7]).
        2: { change [2; 2; 3; 5; 7; 7; 11] with ([2; 2; 3; 5; 7; 7] ++ 11 :: []). apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_cons.
        transitivity (5 :: [2; 3; 7; 7]).
        2: { change [2; 3; 5; 7; 7] with ([2; 3] ++ 5 :: [7; 7]). apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_cons.
        transitivity (7 :: [3; 7]).
        2: { apply Permutation_swap. }
        apply Permutation_cons.
        transitivity (7 :: [3]).
        2: { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.