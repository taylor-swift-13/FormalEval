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
  [5; -2; -12; 4; 2; 23; 2; 3; -13; 11; 12; -10; 3; 2; 4; -10; 3] 
  [-13; -2; -12; 4; 2; 23; 2; 3; 3; 11; 3; -10; 4; 2; 5; -10; 12].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 18 (destruct i; [ simpl in Hodd; try discriminate; simpl; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [5; -12; 2; 2; -13; 12; 3; 4; 3] with ([5; -12; 2; 2] ++ -13 :: [12; 3; 4; 3]).
        apply Permutation_trans with (l' := -13 :: ([5; -12; 2; 2] ++ [12; 3; 4; 3])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        change [5; -12; 2; 2; 12; 3; 4; 3] with ([5] ++ -12 :: [2; 2; 12; 3; 4; 3]).
        apply Permutation_trans with (l' := -12 :: ([5] ++ [2; 2; 12; 3; 4; 3])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        change [5; 2; 2; 12; 3; 4; 3] with ([5] ++ 2 :: [2; 12; 3; 4; 3]).
        apply Permutation_trans with (l' := 2 :: ([5] ++ [2; 12; 3; 4; 3])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        change [5; 2; 12; 3; 4; 3] with ([5] ++ 2 :: [12; 3; 4; 3]).
        apply Permutation_trans with (l' := 2 :: ([5] ++ [12; 3; 4; 3])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        change [5; 12; 3; 4; 3] with ([5; 12] ++ 3 :: [4; 3]).
        apply Permutation_trans with (l' := 3 :: ([5; 12] ++ [4; 3])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        change [5; 12; 4; 3] with ([5; 12; 4] ++ 3 :: []).
        apply Permutation_trans with (l' := 3 :: ([5; 12; 4] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        change [5; 12; 4] with ([5; 12] ++ 4 :: []).
        apply Permutation_trans with (l' := 4 :: ([5; 12] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil || lia).
Qed.