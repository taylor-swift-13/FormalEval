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
  [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 11; 16; 17; 18; 20; 20; 7; 8; 6] 
  [1; 2; 3; 4; 5; 6; 6; 8; 10; 7; 12; 13; 11; 11; 16; 14; 18; 20; 17; 7; 8; 20].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; compute in H; discriminate);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        do 2 apply perm_skip.
        apply Permutation_middle.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; compute; discriminate || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.