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
  [1; 5; 3; -5; 23; -3; 3; -9; 0; 23; 123; -1; -10; 5] 
  [-10; 5; 0; -5; 1; -3; 3; -9; 3; 23; 23; -1; 123; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -10 :: [1; 3; 23; 3; 0; 123]).
        { apply Permutation_sym.
          rewrite <- (app_nil_r [1; 3; 23; 3; 0; 123]).
          apply Permutation_cons_app. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 0 :: [1; 3; 23; 3; 123]).
        { apply Permutation_sym.
          change [1; 3; 23; 3; 0; 123] with ([1; 3; 23; 3] ++ 0 :: [123]).
          apply Permutation_cons_app. }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.