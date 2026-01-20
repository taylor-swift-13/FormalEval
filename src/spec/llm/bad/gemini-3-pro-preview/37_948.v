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
  [5; 3; 10; -5; 2; -3; -9; -10; 0; 123; 1; -10; 10; -5; -3] 
  [-9; 3; -3; -5; 0; -3; 1; -10; 2; 123; 5; -10; 10; -5; 10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -9 :: [5; 10; 2] ++ [0; 1; 10; -3]).
        { apply Permutation_sym. simpl. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := -3 :: [5; 10; 2; 0; 1; 10] ++ []).
        { apply Permutation_sym. rewrite app_nil_r. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := 0 :: [5; 10; 2] ++ [1; 10]).
        { apply Permutation_sym. simpl. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := 1 :: [5; 10; 2] ++ [10]).
        { apply Permutation_sym. simpl. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := 2 :: [5; 10] ++ [10]).
        { apply Permutation_sym. simpl. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.