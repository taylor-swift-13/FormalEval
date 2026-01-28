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
  [5; 3; -5; 2; -2; 3; -9; 1; 0; 123; 1; 9; -10; 12] 
  [-10; 3; -9; 2; -5; 3; -2; 1; 0; 123; 1; 9; 5; 12].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 14 (destruct i; [
        simpl in Hodd;
        try discriminate Hodd;
        simpl; reflexivity
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [5; -5; -2; -9; 0; 1; -10] *)
        (* RHS: [-10; -9; -5; -2; 0; 1; 5] *)
        
        (* Move -10 to front *)
        transitivity ([-10] ++ [5; -5; -2; -9; 0; 1]).
        { change [5; -5; -2; -9; 0; 1; -10] with ([5; -5; -2; -9; 0; 1] ++ [-10]).
          apply Permutation_app_comm. }
        simpl. apply perm_skip.
        
        (* Move -9 to front *)
        transitivity ([-9] ++ [5; -5; -2] ++ [0; 1]).
        { change [5; -5; -2; -9; 0; 1] with ([5; -5; -2] ++ [-9] ++ [0; 1]).
          symmetry. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move -5 to front *)
        transitivity ([-5] ++ [5] ++ [-2; 0; 1]).
        { change [5; -5; -2; 0; 1] with ([5] ++ [-5] ++ [-2; 0; 1]).
          symmetry. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move -2 to front *)
        transitivity ([-2] ++ [5] ++ [0; 1]).
        { change [5; -2; 0; 1] with ([5] ++ [-2] ++ [0; 1]).
          symmetry. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 0 to front *)
        transitivity ([0] ++ [5] ++ [1]).
        { change [5; 0; 1] with ([5] ++ [0] ++ [1]).
          symmetry. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Swap 1 and 5 *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.