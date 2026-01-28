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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; -200; -901; 800; 200] 
  [-200; 500; 6; 4; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 200; -901; 800; 300].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [
        vm_compute in H; try contradiction;
        vm_compute; reflexivity
      | ]).
      vm_compute. reflexivity.
    + split.
      * vm_compute.
        apply (Permutation_cons_app _ _ [300; 7; 20; 104; 4] [200] (-200)); simpl.
        apply (Permutation_cons_app _ _ [300; 7; 20; 104] [200] 4); simpl.
        apply (Permutation_cons_app _ _ [300] [20; 104; 200] 7); simpl.
        apply (Permutation_cons_app _ _ [300] [104; 200] 20); simpl.
        apply (Permutation_cons_app _ _ [300] [200] 104); simpl.
        apply (Permutation_cons_app _ _ [300] [] 200); simpl.
        apply (Permutation_cons_app _ _ [] [] 300); simpl.
        apply Permutation_nil.
      * vm_compute.
        repeat constructor.
Qed.