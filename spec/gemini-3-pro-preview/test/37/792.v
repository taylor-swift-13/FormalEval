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
  [2; 3; 1; 2; 9; 6; 7; 6; 8; 2; 9; 6] 
  [1; 3; 2; 2; 7; 6; 8; 6; 9; 2; 9; 6].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Exhaustively check indices 0 to 11 *)
      do 12 (destruct i; [ 
        try (simpl in Hodd; discriminate Hodd); 
        try (simpl; reflexivity)
        | ]).
      (* Case i >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [2; 1; 9; 7; 8; 9] [1; 2; 7; 8; 9; 9] *)
        apply Permutation_trans with (l' := 1 :: 2 :: [9; 7; 8; 9]).
        { apply perm_swap. }
        apply perm_skip. (* Skips 1 *)
        apply perm_skip. (* Skips 2 *)
        (* Goal: Permutation [9; 7; 8; 9] [7; 8; 9; 9] *)
        apply Permutation_trans with (l' := 7 :: 9 :: [8; 9]).
        { apply perm_swap. }
        apply perm_skip. (* Skips 7 *)
        (* Goal: Permutation [9; 8; 9] [8; 9; 9] *)
        apply Permutation_trans with (l' := 8 :: 9 :: [9]).
        { apply perm_swap. }
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.