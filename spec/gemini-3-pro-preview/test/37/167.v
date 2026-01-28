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

Example test_sort_even_case : sort_even_spec [5; -2; -12; 4; 4; 123; 23; 2; 3; 11; 12; -10] [-12; -2; 3; 4; 4; 123; 5; 2; 12; 11; 23; -10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 6 (destruct i; [ simpl in Hodd; discriminate Hodd | destruct i; [ simpl; reflexivity | ] ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_trans with (l' := -12 :: 5 :: 4 :: 23 :: 3 :: 12 :: []).
        apply perm_swap.
        apply perm_skip.
        apply perm_trans with (l' := 3 :: 5 :: 4 :: 23 :: 12 :: []).
        apply Permutation_sym. apply (Permutation_middle [5; 4; 23] [12] 3).
        apply perm_skip.
        apply perm_trans with (l' := 4 :: 5 :: 23 :: 12 :: []).
        apply perm_swap.
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_cons; lia | apply HdRel_nil ] ]).
        apply Sorted_nil.
Qed.