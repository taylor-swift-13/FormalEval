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
  [32; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 88; 11; 12; 13; 14; 15] 
  [3; 1; 2; 6; 4; 5; 9; 7; 8; 11; 10; 88; 14; 12; 13; 32; 15].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [ try (simpl in H; congruence); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [3; 6; 9; 11; 14; 32] with ([3; 6; 9; 11; 14] ++ [32]).
        change [32; 3; 6; 9; 11; 14] with ([32] ++ [3; 6; 9; 11; 14]).
        apply Permutation_app_comm.
      * simpl.
        repeat apply Sorted_cons; try apply Sorted_nil; try apply HdRel_nil; 
        try (constructor; unfold Z.le; vm_compute; discriminate).
Qed.