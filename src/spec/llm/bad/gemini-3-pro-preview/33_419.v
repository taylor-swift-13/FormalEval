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
  [300; 500; 16; 7; 8; 289; 21; -105; -277; 200; 4; 5; 700; -200; -901; 800; 1000; 300] 
  [7; 500; 16; 21; 8; 289; 200; -105; -277; 300; 4; 5; 700; -200; -901; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil).
        all: try apply HdRel_nil.
        all: try (apply HdRel_cons; compute; discriminate).
Qed.