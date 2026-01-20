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
  [5; 3; -5; -4; 2; -3; 3; -9; 0; 123; 1; 123; 3] 
  [-5; 3; 0; -4; 1; -3; 2; -9; 3; 123; 3; 123; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [ 
        simpl in Hodd; 
        try discriminate; 
        try (simpl; reflexivity) 
      | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        (* Sort the left list to match the right list [-5; 0; 1; 2; 3; 3; 5] *)
        
        (* Move -5 to front *)
        apply Permutation_trans with (l' := -5 :: [5; 2; 3; 0; 1; 3]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move 0 to front *)
        apply Permutation_trans with (l' := 0 :: [5; 2; 3; 1; 3]).
        { 
          change (5 :: 2 :: 3 :: 0 :: 1 :: 3 :: []) with (5 :: 2 :: (3 :: 0 :: 1 :: 3 :: [])).
          apply Permutation_trans with (l' := 5 :: 2 :: 0 :: 3 :: 1 :: 3 :: []).
          { repeat apply perm_skip. apply perm_swap. }
          apply Permutation_trans with (l' := 5 :: 0 :: 2 :: 3 :: 1 :: 3 :: []).
          { apply perm_skip. apply perm_swap. }
          apply perm_swap.
        }
        apply perm_skip.

        (* Move 1 to front *)
        apply Permutation_trans with (l' := 1 :: [5; 2; 3; 3]).
        {
          change (5 :: 2 :: 3 :: 1 :: 3 :: []) with (5 :: 2 :: (3 :: 1 :: 3 :: [])).
          apply Permutation_trans with (l' := 5 :: 2 :: 1 :: 3 :: 3 :: []).
          { repeat apply perm_skip. apply perm_swap. }
          apply Permutation_trans with (l' := 5 :: 1 :: 2 :: 3 :: 3 :: []).
          { apply perm_skip. apply perm_swap. }
          apply perm_swap.
        }
        apply perm_skip.

        (* Move 2 to front *)
        apply Permutation_trans with (l' := 2 :: [5; 3; 3]).
        { apply perm_swap. }
        apply perm_skip.

        (* Move 3 to front *)
        apply Permutation_trans with (l' := 3 :: [5; 3]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Swap 5 and 3 *)
        apply perm_swap.

      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.