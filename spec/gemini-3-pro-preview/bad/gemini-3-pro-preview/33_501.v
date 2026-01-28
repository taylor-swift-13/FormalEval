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
  [19; 0; -901; 2; 3; 4; 5; 6; 16; 7; 8; 10; 10; 11; 12; 14; 15; 16; 17; 18; 19; 21; 20; 16]
  [2; 0; -901; 5; 3; 4; 7; 6; 16; 10; 8; 10; 14; 11; 12; 17; 15; 16; 19; 18; 19; 21; 20; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 25 (destruct i as [|i]; [ 
        simpl in *; 
        try (match goal with | H : _ <> 0 |- _ => compute in H; contradiction end);
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        apply Permutation_sym.
        apply (Permutation_cons_app 19 [2; 5; 7; 10; 14; 17] [21]).
        simpl. apply Permutation_refl.
      * vm_compute.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.