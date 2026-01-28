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

Example test_sort_even_case : sort_even_spec [11; -7; 2; 10; 2; 9; 5; -3; 2; 8; 3; 7] [2; -7; 2; 10; 2; 9; 3; -3; 5; 8; 11; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [2; 11; 2; 5; 2; 3]). apply perm_swap.
        apply perm_skip.
        apply Permutation_trans with (l' := [2; 11; 5; 2; 3]). apply perm_swap.
        apply perm_skip.
        apply Permutation_trans with (l' := [11; 2; 5; 3]). apply perm_skip. apply perm_swap.
        apply Permutation_trans with (l' := [2; 11; 5; 3]). apply perm_swap.
        apply perm_skip.
        apply Permutation_trans with (l' := [11; 3; 5]). apply perm_skip. apply perm_swap.
        apply Permutation_trans with (l' := [3; 11; 5]). apply perm_swap.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.