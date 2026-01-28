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
  [-7; 2; 10; 0; 9; 5; -5; 2; 8; 3; 7; 9] 
  [-7; 2; -5; 0; 7; 5; 8; 2; 9; 3; 10; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (-5 :: [10; 9; 8; 7]).
        { change [10; 9; -5; 8; 7] with ([10; 9] ++ -5 :: [8; 7]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        transitivity (7 :: [10; 9; 8]).
        { change [10; 9; 8; 7] with ([10; 9; 8] ++ 7 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        transitivity (8 :: [10; 9]).
        { change [10; 9; 8] with ([10; 9] ++ 8 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.