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

Example test_sort_even_case : sort_even_spec [6; 3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 3; 6] [1; 3; 1; 4; 3; 5; 6; 2; 6; 5; 6; 3; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ 
        try (simpl in Hodd; discriminate Hodd); try (simpl; reflexivity) 
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 1 :: 6 :: 1 :: 9 :: 6 :: 3 :: 6 :: nil).
        apply perm_swap. apply perm_skip.
        apply Permutation_trans with (l' := 1 :: 6 :: 9 :: 6 :: 3 :: 6 :: nil).
        apply perm_swap. apply perm_skip.
        apply Permutation_trans with (l' := 6 :: 9 :: 3 :: 6 :: 6 :: nil).
        apply perm_skip. apply perm_skip. apply perm_swap.
        apply Permutation_trans with (l' := 6 :: 3 :: 9 :: 6 :: 6 :: nil).
        apply perm_skip. apply perm_swap.
        apply Permutation_trans with (l' := 3 :: 6 :: 9 :: 6 :: 6 :: nil).
        apply perm_swap.
        apply perm_skip. apply perm_skip.
        apply Permutation_trans with (l' := 6 :: 9 :: 6 :: nil).
        apply perm_swap.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.