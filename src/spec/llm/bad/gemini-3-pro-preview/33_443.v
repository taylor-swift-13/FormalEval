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
  [1; 2; 3; -3; 5; 16; 16; -8; 9; -12; 7; 6; -12] 
  [-12; 2; 3; -12; 5; 16; -3; -8; 9; 1; 7; 6; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i as [|i]; [
        simpl in H; try contradiction; try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-12 :: [1; -3; 16; -12]).
        { apply Permutation_cons.
          transitivity (-12 :: [1; -3; 16]).
          { apply Permutation_cons.
            transitivity (-3 :: [1; 16]).
            { apply Permutation_cons. apply Permutation_refl. }
            { apply Permutation_sym, Permutation_middle. } }
          { apply Permutation_sym, Permutation_middle. } }
        { apply Permutation_sym, Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ try apply HdRel_nil; apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.