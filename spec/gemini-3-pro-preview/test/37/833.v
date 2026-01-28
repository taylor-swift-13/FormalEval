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

Example test_sort_even_case : sort_even_spec [5; 0; 5; 5; 0; 5; 0; 5; 5; 0; 0] [0; 0; 0; 5; 0; 5; 5; 5; 5; 0; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 5; 0; 0; 5; 0] [0; 0; 0; 5; 5; 5] *)
        (* Strategy: Move 0s to front in LHS using Permutation_middle symmetry *)
        
        assert (H1: Permutation [5; 5; 0; 0; 5; 0] (0 :: [5; 5] ++ [0; 5; 0])).
        { change [5; 5; 0; 0; 5; 0] with ([5; 5] ++ 0 :: [0; 5; 0]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H1. simpl. apply perm_skip.
        
        assert (H2: Permutation [5; 5; 0; 5; 0] (0 :: [5; 5] ++ [5; 0])).
        { change [5; 5; 0; 5; 0] with ([5; 5] ++ 0 :: [5; 0]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H2. simpl. apply perm_skip.
        
        assert (H3: Permutation [5; 5; 5; 0] (0 :: [5; 5; 5] ++ [])).
        { change [5; 5; 5; 0] with ([5; 5; 5] ++ 0 :: []).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H3. simpl. apply perm_skip.
        
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat constructor; try lia.
Qed.