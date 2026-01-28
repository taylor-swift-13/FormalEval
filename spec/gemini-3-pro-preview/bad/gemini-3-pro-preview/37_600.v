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
  [2; 2; 3; 4; 11; 6; 7; 7; 8; 2; 2; 7; 6] 
  [2; 2; 2; 4; 3; 6; 6; 7; 7; 2; 8; 7; 11].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [
        simpl in Hodd; try discriminate; simpl; reflexivity
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (3 :: [2] ++ [6; 7; 8; 11]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (11 :: [2; 6; 7; 8] ++ []).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (7 :: [2; 6] ++ [8]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (8 :: [2; 6] ++ []).
        2: apply Permutation_middle.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.