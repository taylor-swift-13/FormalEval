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
  [6; 5; 3; 0; 5; 5; 0; -1; 5; 5; 0; 5] 
  [0; 5; 0; 0; 3; 5; 5; -1; 5; 5; 6; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        assert (H1: Permutation [6; 3; 5; 0; 5; 0] (0 :: [6; 3; 5; 5; 0])).
        { replace [6; 3; 5; 0; 5; 0] with ([6; 3; 5] ++ 0 :: [5; 0]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (l' := 0 :: [6; 3; 5; 5; 0]); [exact H1 | apply perm_skip].

        assert (H2: Permutation [6; 3; 5; 5; 0] (0 :: [6; 3; 5; 5])).
        { replace [6; 3; 5; 5; 0] with ([6; 3; 5; 5] ++ 0 :: []) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (l' := 0 :: [6; 3; 5; 5]); [exact H2 | apply perm_skip].

        assert (H3: Permutation [6; 3; 5; 5] (3 :: [6; 5; 5])).
        { replace [6; 3; 5; 5] with ([6] ++ 3 :: [5; 5]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (l' := 3 :: [6; 5; 5]); [exact H3 | apply perm_skip].

        assert (H4: Permutation [6; 5; 5] (5 :: [6; 5])).
        { replace [6; 5; 5] with ([6] ++ 5 :: [5]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (l' := 5 :: [6; 5]); [exact H4 | apply perm_skip].

        apply perm_swap.
      * simpl. repeat constructor; lia.
Qed.