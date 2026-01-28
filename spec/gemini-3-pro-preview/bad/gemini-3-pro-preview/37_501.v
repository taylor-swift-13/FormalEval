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
  [2; 1; 2; 6; 1; 2; 3; 4; 5; 6; 7; 2; 1; 4; 2] 
  [1; 1; 1; 6; 2; 2; 2; 4; 2; 6; 3; 2; 5; 4; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (2 :: [1; 1] ++ [2; 2; 3; 5; 7]). 2: apply Permutation_middle. apply Permutation_cons.
        transitivity (2 :: [1; 1] ++ [2; 3; 5; 7]). 2: apply Permutation_middle. apply Permutation_cons.
        apply Permutation_cons.
        transitivity (3 :: [1; 2] ++ [5; 7]). 2: apply Permutation_middle. apply Permutation_cons.
        transitivity (5 :: [1; 2] ++ [7]). 2: apply Permutation_middle. apply Permutation_cons.
        transitivity (7 :: [1; 2] ++ []). 2: apply Permutation_middle. apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
      * simpl.
        repeat apply Sorted_cons.
        all: try apply HdRel_cons; try apply HdRel_nil; try apply Sorted_nil; try lia.
Qed.