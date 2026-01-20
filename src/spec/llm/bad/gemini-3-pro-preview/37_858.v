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

Example test_sort_even_case : sort_even_spec [1; 2; 3; 2; -6; -1; 6; -1; 7; 8; 2] [-6; 2; 1; 2; 2; -1; 3; -1; 6; 8; 7].
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
        change [-6; 1; 2; 3; 6; 7] with ([-6] ++ 1 :: [2; 3; 6; 7]).
        apply Permutation_trans with (l' := 1 :: [-6] ++ [2; 3; 6; 7]); [ | apply Permutation_middle ].
        constructor.
        change [-6; 2; 3; 6; 7] with ([-6; 2] ++ 3 :: [6; 7]).
        apply Permutation_trans with (l' := 3 :: [-6; 2] ++ [6; 7]); [ | apply Permutation_middle ].
        constructor.
        constructor.
        change [2; 6; 7] with ([2] ++ 6 :: [7]).
        apply Permutation_trans with (l' := 6 :: [2] ++ [7]); [ | apply Permutation_middle ].
        constructor.
        change [2; 7] with ([2] ++ 7 :: []).
        apply Permutation_trans with (l' := 7 :: [2] ++ []); [ | apply Permutation_middle ].
        constructor.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; simpl; try lia).
Qed.