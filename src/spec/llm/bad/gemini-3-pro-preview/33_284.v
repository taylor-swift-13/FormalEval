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
  [-4; 7; 105; 3; 3; 0; 7; -8; -2; 2; 0; 1; 20; 0; 0; 1] 
  [-4; 7; 105; 1; 3; 0; 2; -8; -2; 3; 0; 1; 7; 0; 0; 20].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i as [|i]; [ 
        simpl in *; 
        try (elim H; reflexivity); 
        reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * unfold extract_thirds.
        vm_compute.
        apply Permutation_cons.
        transitivity (1 :: [3; 7; 2; 20]).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        transitivity (2 :: [3; 7] ++ [20]).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        simpl. apply Permutation_refl.
      * unfold extract_thirds.
        vm_compute.
        repeat constructor; unfold Z.le; simpl; intro Hc; discriminate.
Qed.