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

Example test_sort_even_case : sort_even_spec [-3; 2; 2; 2; 4; 6; 7; 8; 2; -7; 1] [-3; 2; 1; 2; 2; 6; 2; 8; 4; -7; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons; [reflexivity | ].
        change [2; 4; 7; 2; 1] with ([2; 4; 7; 2] ++ [1]).
        transitivity (1 :: [2; 4; 7; 2]).
        { apply Permutation_sym. apply (Permutation_middle [2; 4; 7; 2] [] 1). }
        apply Permutation_cons; [reflexivity | ].
        apply Permutation_cons; [reflexivity | ].
        change [4; 7; 2] with ([4; 7] ++ [2]).
        transitivity (2 :: [4; 7]).
        { apply Permutation_sym. apply (Permutation_middle [4; 7] [] 2). }
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try lia).
Qed.