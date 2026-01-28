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
  [5; -2; -12; 4; 23; 2; 3; -13; 11; 12; -10; 3; 2; 4] 
  [-12; -2; -10; 4; 2; 2; 3; -13; 5; 12; 11; 3; 23; 4].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Destruct i enough times to cover the list indices (0 to 13) *)
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 14, length check fails *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -12; 23; 3; 11; -10; 2] [-12; -10; 2; 3; 5; 11; 23] *)
        
        (* Move -12 to front *)
        apply Permutation_trans with (l' := -12 :: [5] ++ [23; 3; 11; -10; 2]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move -10 to front *)
        apply Permutation_trans with (l' := -10 :: [5; 23; 3; 11] ++ [2]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 2 to front *)
        apply Permutation_trans with (l' := 2 :: [5; 23; 3; 11] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. rewrite app_nil_r. apply perm_skip.
        
        (* Move 3 to front *)
        apply Permutation_trans with (l' := 3 :: [5; 23] ++ [11]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 5 (already at front of remainder [5; 23; 11] vs [5; 11; 23]) *)
        apply perm_skip.
        
        (* Swap 23 and 11 *)
        apply perm_swap.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; simpl; try lia).
Qed.