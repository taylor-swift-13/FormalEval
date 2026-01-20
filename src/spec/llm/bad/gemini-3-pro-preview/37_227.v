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

Example test_sort_even_case_2 : sort_even_spec 
  [-5; -7; 2; 10; 9; -3; 2; 8; 3; 7; 2; 8; 2] 
  [-5; -7; 2; 10; 2; -3; 2; 8; 2; 7; 3; 8; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        apply perm_skip.
        apply perm_skip.
        transitivity (2 :: 9 :: 3 :: 2 :: 2). apply Permutation_swap.
        apply perm_skip.
        transitivity (9 :: 2 :: 3 :: 2). apply perm_skip. apply Permutation_swap.
        transitivity (2 :: 9 :: 3 :: 2). apply Permutation_swap.
        apply perm_skip.
        transitivity (9 :: 2 :: 3). apply perm_skip. apply Permutation_swap.
        transitivity (2 :: 9 :: 3). apply Permutation_swap.
        apply perm_skip.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.