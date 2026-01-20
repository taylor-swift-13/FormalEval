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
  [-5; -7; 2; -5; 2; 9; 5; -3; 2; 8; 7; 3; 7; 12; 2] 
  [-5; -7; 2; -5; 2; 9; 2; -3; 2; 8; 5; 3; 7; 12; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 14 *)
      do 15 (destruct i; [
        simpl in Hodd;
        try discriminate Hodd;
        simpl; reflexivity
      | ]).
      (* For i >= 15, length check fails *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Input evens: [-5; 2; 2; 5; 2; 7; 7; 2] *)
        (* Output evens: [-5; 2; 2; 2; 2; 5; 7; 7] *)
        apply perm_skip. apply perm_skip. apply perm_skip.
        (* Goal: Permutation [5; 2; 7; 7; 2] [2; 2; 5; 7; 7] *)
        (* Bring the first 2 (at index 1) to the front *)
        apply perm_trans with (2 :: 5 :: 7 :: 7 :: 2 :: nil).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [5; 7; 7; 2] [2; 5; 7; 7] *)
        (* Bring the last 2 (at index 3) to the front *)
        apply perm_trans with (5 :: 7 :: 2 :: 7 :: nil).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_trans with (5 :: 2 :: 7 :: 7 :: nil).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.