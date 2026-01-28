Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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
  [5; 2; 7; 299; 3; -7; 11; 8; 0; 1; 13; 6; -2; 19; 2] 
  [-2; 2; 7; 1; 3; -7; 5; 8; 0; 11; 13; 6; 299; 19; 2].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-2 :: [5; 299; 11; 1]).
        { apply perm_skip.
          transitivity (1 :: [5; 299; 11]).
          { apply perm_skip.
            apply perm_skip.
            apply perm_swap. }
          { apply Permutation_sym. apply (Permutation_middle _ [5; 299; 11] [] 1). } }
        { apply Permutation_sym. apply (Permutation_middle _ [5; 299; 11; 1] [] (-2)). }
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; simpl; lia | ]).
        apply Sorted_nil.
Qed.