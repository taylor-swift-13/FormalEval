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

Example test_sort_even_case : sort_even_spec [1; 2; 4; 2; -6; -1; -4; 6; -6; 3; -1; 7; 8; 2] [-6; 2; -6; 2; -4; -1; -1; 6; 1; 3; 4; 7; 8; 2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (-6 :: [1; 4] ++ [-4; -6; -1; 8]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        transitivity (-6 :: [1; 4; -4] ++ [-1; 8]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        transitivity (-4 :: [1; 4] ++ [-1; 8]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        transitivity (-1 :: [1; 4] ++ [8]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.