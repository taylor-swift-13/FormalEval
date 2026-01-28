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
  [-5; -7; 2; -5; 2; 9; 5; -3; 2; 8; 7; 3; 7; 2; 2] 
  [-5; -7; 2; -5; 2; 9; 2; -3; 2; 8; 5; 3; 7; 2; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        do 3 apply perm_skip.
        apply perm_trans with (l' := [2; 5; 7; 7; 2]).
        apply perm_swap.
        apply perm_skip.
        apply perm_trans with (l' := [5; 7; 2; 7]).
        do 2 apply perm_skip. apply perm_swap.
        apply perm_trans with (l' := [5; 2; 7; 7]).
        apply perm_skip. apply perm_swap.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.