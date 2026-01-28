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
  [2; -3; 5; 1; 0; 18; 4; 9; -12; 0; 7; 6] 
  [0; -3; 5; 1; 0; 18; 2; 9; -12; 4; 7; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i as [|i]; [
        simpl in H; try contradiction; simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [2; 1; 4; 0] with ([2; 1; 4] ++ [0]).
        apply Permutation_trans with (l' := [0; 2; 1; 4]).
        { apply Permutation_cons. constructor 2. apply Permutation_refl. }
        { apply Permutation_app_comm. }
      * simpl.
        repeat (apply Sorted_cons; [
          try apply HdRel_nil; try apply HdRel_cons; compute; try (intro; discriminate)
        | ]).
        apply Sorted_nil.
Qed.