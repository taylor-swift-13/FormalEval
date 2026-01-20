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
  [5; 3; 6; -11; -5; 2; -3; -9; 0; 123; 1; -10; 3; 123; -9] 
  [-9; 3; -5; -11; -3; 2; 0; -9; 1; 123; 3; -10; 5; 123; 6].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 20 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity ([-9; -5; -3; 0; 1; 3] ++ 5 :: [6]).
        { simpl. reflexivity. }
        transitivity (5 :: [-9; -5; -3; 0; 1; 3] ++ [6]).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        transitivity ([-9; -5; -3; 0; 1; 3] ++ 6 :: []).
        { simpl. reflexivity. }
        transitivity (6 :: [-9; -5; -3; 0; 1; 3] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        transitivity ([-9] ++ -5 :: [-3; 0; 1; 3]).
        { simpl. reflexivity. }
        transitivity (-5 :: [-9] ++ [-3; 0; 1; 3]).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        transitivity ([-9] ++ -3 :: [0; 1; 3]).
        { simpl. reflexivity. }
        transitivity (-3 :: [-9] ++ [0; 1; 3]).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        transitivity ([-9] ++ 0 :: [1; 3]).
        { simpl. reflexivity. }
        transitivity (0 :: [-9] ++ [1; 3]).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        transitivity ([-9] ++ 1 :: [3]).
        { simpl. reflexivity. }
        transitivity (1 :: [-9] ++ [3]).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        transitivity ([-9] ++ 3 :: []).
        { simpl. reflexivity. }
        transitivity (3 :: [-9] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        constructor.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.