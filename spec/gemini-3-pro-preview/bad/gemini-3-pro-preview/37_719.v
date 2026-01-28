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
  [-5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 10; 3; 7; 2; -3] 
  [-5; -7; -3; 10; 0; 9; 2; -3; 2; 8; 5; 3; 7; 2; 10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (-3 :: [2; 0; 5; 2; 10; 7]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (0 :: [2; 5; 2; 10; 7]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_cons.
        transitivity (2 :: [5; 10; 7]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat constructor; try lia.
Qed.