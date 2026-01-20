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
  [5; -2; -12; 2; 4; 23; 2; 3; 11; 12; -9; 3; 3] 
  [-12; -2; -9; 2; 2; 23; 3; 3; 4; 12; 5; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Exhaustively check indices 0 to 12 *)
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 13, contradict length *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -12; 4; 2; 11; -9; 3] [-12; -9; 2; 3; 4; 5; 11] *)
        
        (* Move -12 to front *)
        transitivity (-12 :: [5; 4; 2; 11; -9; 3]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move -9 to front *)
        transitivity (5 :: 4 :: 2 :: -9 :: 11 :: 3 :: []).
        { do 3 apply perm_skip. apply perm_swap. }
        transitivity (5 :: 4 :: -9 :: 2 :: 11 :: 3 :: []).
        { do 2 apply perm_skip. apply perm_swap. }
        transitivity (5 :: -9 :: 4 :: 2 :: 11 :: 3 :: []).
        { apply perm_skip. apply perm_swap. }
        transitivity (-9 :: 5 :: 4 :: 2 :: 11 :: 3 :: []).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move 2 to front *)
        transitivity (5 :: 2 :: 4 :: 11 :: 3 :: []).
        { apply perm_skip. apply perm_swap. }
        transitivity (2 :: 5 :: 4 :: 11 :: 3 :: []).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move 3 to front *)
        transitivity (5 :: 4 :: 3 :: 11 :: []).
        { do 2 apply perm_skip. apply perm_swap. }
        transitivity (5 :: 3 :: 4 :: 11 :: []).
        { apply perm_skip. apply perm_swap. }
        transitivity (3 :: 5 :: 4 :: 11 :: []).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move 4 to front *)
        transitivity (4 :: 5 :: 11 :: []).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Remaining [5; 11] matches *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.