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
  [-7; 2; 3; 4; 5; 6; -2; 7; 10; 2; 4] 
  [-7; 2; -2; 4; 3; 6; 4; 7; 5; 2; 10].
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
        apply Permutation_cons.
        change [3; 5; -2; 10; 4] with ([3; 5] ++ -2 :: [10; 4]).
        transitivity (-2 :: [3; 5] ++ [10; 4]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        apply Permutation_cons.
        change [5; 10; 4] with ([5; 10] ++ 4 :: []).
        transitivity (4 :: [5; 10] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.