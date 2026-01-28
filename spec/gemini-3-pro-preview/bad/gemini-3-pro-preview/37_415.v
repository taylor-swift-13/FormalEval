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
  [5; 3; -5; 5; -3; -2; 3; -9; 0; 1; -10; -9] 
  [-10; 3; -5; 5; -3; -2; 0; -9; 3; 1; 5; -9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 11 *)
      do 12 (destruct i; [
        try (simpl in Hodd; discriminate); (* Even indices *)
        try (simpl; reflexivity)           (* Odd indices *)
      | ]).
      (* Indices >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -5; -3; 3; 0; -10] [-10; -5; -3; 0; 3; 5] *)
        
        (* Move -10 to front *)
        change [5; -5; -3; 3; 0; -10] with ([5; -5; -3; 3; 0] ++ [-10]).
        transitivity ([-10] ++ [5; -5; -3; 3; 0]).
        { apply Permutation_app_comm. }
        simpl. apply perm_skip.
        
        (* Goal: Permutation [5; -5; -3; 3; 0] [-5; -3; 0; 3; 5] *)
        (* Move -5 to front *)
        transitivity (-5 :: 5 :: -3 :: 3 :: 0).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Goal: Permutation [5; -3; 3; 0] [-3; 0; 3; 5] *)
        (* Move -3 to front *)
        transitivity (-3 :: 5 :: 3 :: 0).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Goal: Permutation [5; 3; 0] [0; 3; 5] *)
        (* Move 0 to front *)
        change [5; 3; 0] with ([5; 3] ++ [0]).
        transitivity ([0] ++ [5; 3]).
        { apply Permutation_app_comm. }
        simpl. apply perm_skip.
        
        (* Goal: Permutation [5; 3] [3; 5] *)
        apply perm_swap.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.