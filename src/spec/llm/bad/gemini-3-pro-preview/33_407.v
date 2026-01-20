Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [5; 2; 7; 9; 3; -7; 11; 8; 0; 700; 1; 13; 6; -2; 19; 19; 13; 9; 13] 
  [5; 2; 7; 6; 3; -7; 9; 8; 0; 11; 1; 13; 13; -2; 19; 19; 13; 9; 700].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [ simpl in *; try reflexivity; try (exfalso; compute in H; discriminate) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_skip.
        transitivity (6 :: [9; 11; 700] ++ [19; 13]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        apply perm_skip.
        apply perm_skip.
        transitivity (13 :: [700; 19] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.