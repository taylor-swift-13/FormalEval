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

Example test_sort_even_case : sort_even_spec [2; 3; 2; 1; 3; 6; 7; 9; -10; 2; 5; 2; 3] [-10; 3; 2; 1; 2; 6; 3; 9; 3; 2; 5; 2; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -10 :: [2; 2; 3; 7; 5; 3]).
        { apply Permutation_sym.
          change [2; 2; 3; 7; -10; 5; 3] with ([2; 2; 3; 7] ++ -10 :: [5; 3]).
          apply Permutation_middle. }
        apply perm_skip.
        apply perm_skip.
        apply perm_skip.
        apply perm_skip.
        apply Permutation_trans with (l' := 3 :: [7; 5]).
        { apply Permutation_sym.
          change [7; 5; 3] with ([7; 5] ++ [3]).
          apply Permutation_cons_app. }
        apply perm_skip.
        apply perm_swap.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.