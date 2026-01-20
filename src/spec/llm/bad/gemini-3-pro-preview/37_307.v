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
  [-5%Z; 4%Z; 2%Z; 2%Z; 0%Z; 9%Z; 5%Z; -3%Z; 2%Z; 8%Z; 3%Z; 7%Z; 4%Z; 2%Z; 2%Z; 8%Z; 2%Z] 
  [-5%Z; 4%Z; 0%Z; 2%Z; 2%Z; 9%Z; 2%Z; -3%Z; 2%Z; 8%Z; 2%Z; 7%Z; 3%Z; 2%Z; 4%Z; 8%Z; 5%Z].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 17 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (0 :: 2 :: [5; 2; 3; 4; 2; 2]). apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_cons.
        transitivity (2 :: 5 :: [3; 4; 2; 2]). apply Permutation_swap.
        apply Permutation_cons.
        transitivity (5 :: 3 :: 2 :: 4 :: 2). do 2 apply Permutation_cons. apply Permutation_swap.
        transitivity (5 :: 2 :: 3 :: 4 :: 2). apply Permutation_cons. apply Permutation_swap.
        transitivity (2 :: 5 :: 3 :: 4 :: 2). apply Permutation_swap.
        apply Permutation_cons.
        transitivity (5 :: 3 :: 2 :: 4). do 2 apply Permutation_cons. apply Permutation_swap.
        transitivity (5 :: 2 :: 3 :: 4). apply Permutation_cons. apply Permutation_swap.
        transitivity (2 :: 5 :: 3 :: 4). apply Permutation_swap.
        apply Permutation_cons.
        transitivity (3 :: 5 :: 4). apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try (simpl; apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.