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
  [1; 15; 2; 3; 4; 5; 19; 6; 7; 8; 10; 11; 1000; 12; 13; 14; 15; 16; 17; 18; 20; 20; 7; 8]
  [1; 15; 2; 3; 4; 5; 8; 6; 7; 14; 10; 11; 17; 12; 13; 19; 15; 16; 20; 18; 20; 1000; 7; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 24 (destruct i; [ 
        simpl in *; 
        try (exfalso; vm_compute in H; congruence); 
        reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_sym; apply Permutation_swap; apply Permutation_sym.
        apply Permutation_cons.
        transitivity [19; 14; 1000; 17; 20].
        2: apply Permutation_cons; apply Permutation_swap.
        apply Permutation_swap.
        apply Permutation_cons.
        transitivity [19; 17; 1000; 20].
        2: apply Permutation_cons; apply Permutation_swap.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; compute; reflexivity | ]).
        apply Sorted_nil.
Qed.