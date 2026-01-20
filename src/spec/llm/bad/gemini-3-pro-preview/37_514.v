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
  [-5; -7; 2; 10; 9; -3; 2; 8; -6; 7; 2; 8; 2] 
  [-6; -7; -5; 10; 2; -3; 2; 8; 2; 7; 2; 8; 9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 12. Even indices are discriminated by Hodd, odd ones checked by reflexivity. *)
      do 13 (destruct i as [|i]; [ try (simpl in Hodd; discriminate); simpl; reflexivity | ]).
      (* Remaining indices >= 13 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [-5; 2; 9; 2; -6; 2; 2] *)
        (* RHS: [-6; -5; 2; 2; 2; 2; 9] *)
        
        (* Strategy: Move -6 (index 4) to front *)
        apply Permutation_trans with (l' := -5 :: 2 :: 9 :: -6 :: 2 :: 2 :: 2 :: []).
        { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -5 :: 2 :: -6 :: 9 :: 2 :: 2 :: 2 :: []).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -5 :: -6 :: 2 :: 9 :: 2 :: 2 :: 2 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -6 :: -5 :: 2 :: 9 :: 2 :: 2 :: 2 :: []).
        { apply perm_swap. }
        
        (* Match head -6 *)
        apply perm_skip.
        
        (* Goal: Permutation [-5; 2; 9; 2; 2; 2] [-5; 2; 2; 2; 2; 9] *)
        (* Match head -5 *)
        apply perm_skip.
        
        (* Goal: Permutation [2; 9; 2; 2; 2] [2; 2; 2; 2; 9] *)
        (* Match head 2 *)
        apply perm_skip.
        
        (* Goal: Permutation [9; 2; 2; 2] [2; 2; 2; 9] *)
        (* Move 9 to end *)
        apply Permutation_trans with (l' := 2 :: 9 :: 2 :: 2 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [9; 2; 2] [2; 2; 9] *)
        apply Permutation_trans with (l' := 2 :: 9 :: 2 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [9; 2] [2; 9] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.