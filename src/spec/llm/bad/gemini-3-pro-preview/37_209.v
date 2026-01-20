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
  [-5; 4; 2; 2; 0; 9; 5; -3; 2; 8; 3; 7; 2; 2; 8] 
  [-5; 4; 0; 2; 2; 9; 2; -3; 2; 8; 3; 7; 5; 2; 8].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        apply Permutation_cons_app. simpl.
        change [0; 2; 2; 2; 3; 5; 8] with ([0] ++ 2 :: [2; 2; 3; 5; 8]).
        apply Permutation_cons_app. simpl.
        apply Permutation_cons_app. simpl.
        change [2; 2; 3; 5; 8] with ([2; 2; 3] ++ 5 :: [8]).
        apply Permutation_cons_app. simpl.
        apply Permutation_cons_app. simpl.
        change [2; 3; 8] with ([2] ++ 3 :: [8]).
        apply Permutation_cons_app. simpl.
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.